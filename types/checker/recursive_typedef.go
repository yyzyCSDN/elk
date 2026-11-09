package checker

import (
	"github.com/elk-language/elk/parser/ast"
	"github.com/elk-language/elk/position"
	"github.com/elk-language/elk/token"
	"github.com/elk-language/elk/types"
)

// This file implements support for transparent recursive typedefs.
//
// Recursive aliases are allowed when every recursive cycle passes through
// one of the mutable container types: ArrayList, ArrayTuple, HashMap or
// HashRecord. Unions, nilable types and non recursive aliases are fully
// transparent and do not protect a cycle. Aliases lying on a cycle must have
// the same number of type parameters and the current parameters have to be
// forwarded positionally and unchanged eg. `A[T] -> B[T]`, `B[U] -> A[U]`.
// Aliases without parameters are treated as having zero parameters.
//
// The resulting types are equi-recursive: the alias unfolds transparently and
// its type graph contains the alias node itself again. Subtype checking is
// done coinductively, so no fixed expansion depth, `any` or `untyped` is ever
// used to check recursive types.

// A single dependency edge between two recursive typedef names.
type typedefCycleEdge struct {
	from     string
	to       string
	guarded  bool // the reference passes through ArrayList/ArrayTuple/HashMap/HashRecord
	hard     bool // the reference passes through any other type constructor
	forwards bool // the reference forwards all current type parameters positionally and unchanged
}

type typedefParamFrame struct {
	params []string
	args   []ast.TypeNode
}

type typedefCycleScanner struct {
	c            *Checker
	targets      map[string]struct{}   // members of the cycle being validated
	infos        map[string]*typedefCycleInfo
	edges        []typedefCycleEdge
	source       string
	sourceParams []string
}

type typedefCycleInfo struct {
	name   string
	params []string
	body   ast.TypeNode
	entry  *typeDefinitionCheckEntry
}

func (c *Checker) collectTypedefCycleEdges(members []string) []typedefCycleEdge {
	targets := make(map[string]struct{}, len(members))
	infos := make(map[string]*typedefCycleInfo, len(members))
	for _, name := range members {
		targets[name] = struct{}{}
		if info := c.typedefCycleInfo(name); info != nil {
			infos[name] = info
		}
	}

	scanner := &typedefCycleScanner{
		c:       c,
		targets: targets,
		infos:   infos,
	}

	for _, name := range members {
		info := infos[name]
		if info == nil {
			continue
		}
		scanner.source = name
		scanner.sourceParams = info.params
		c.withTypeDefinitionScopes(info.entry, func() {
			scanner.walk(info.body, false, false, nil, map[string]struct{}{})
		})
	}

	return scanner.edges
}

func (c *Checker) typedefCycleInfo(name string) *typedefCycleInfo {
	check, ok := c.typeDefinitionChecks.m[name]
	if !ok {
		return nil
	}

	for _, entry := range check.entries {
		switch n := entry.node.(type) {
		case *ast.TypeDefinitionNode:
			return &typedefCycleInfo{
				name:  name,
				body:  n.TypeNode,
				entry: entry,
			}
		case *ast.GenericTypeDefinitionNode:
			params := make([]string, 0, len(n.TypeParameters))
			for _, param := range n.TypeParameters {
				if varNode, ok := param.(*ast.VariantTypeParameterNode); ok {
					params = append(params, varNode.Name)
				}
			}
			return &typedefCycleInfo{
				name:   name,
				params: params,
				body:   n.TypeNode,
				entry:  entry,
			}
		}
	}

	return nil
}

func (c *Checker) withTypeDefinitionScopes(entry *typeDefinitionCheckEntry, fn func()) {
	if entry == nil {
		fn()
		return
	}

	oldFilename := c.Filename
	oldConstantScopes := c.constantScopes
	c.Filename = entry.filename
	c.constantScopes = entry.constantScopes
	defer func() {
		c.Filename = oldFilename
		c.constantScopes = oldConstantScopes
	}()

	fn()
}

func (s *typedefCycleScanner) resolve(node ast.ComplexConstantNode) types.Type {
	return s.c.getComplexConstantTypeForMacro(node)
}

func (s *typedefCycleScanner) isGuardContainer(typ types.Type) bool {
	class, ok := typ.(*types.Class)
	if !ok {
		return false
	}

	switch class.Name() {
	case s.c.StdArrayList().Name(),
		s.c.StdArrayTuple().Name(),
		s.c.StdHashMap().Name(),
		s.c.StdHashRecord().Name():
		return true
	default:
		return false
	}
}

// Resolve the given parameter name through the helper parameter frames.
// Returns the final constant name when the chain ends in a bare constant.
func resolveThroughFrames(name string, frames []typedefParamFrame) (string, bool) {
	for i := len(frames) - 1; i >= 0; i-- {
		frame := frames[i]
		for j, param := range frame.params {
			if param != name {
				continue
			}
			if j >= len(frame.args) {
				return "", false
			}
			arg, ok := frame.args[j].(*ast.PublicConstantNode)
			if !ok {
				return "", false
			}
			return resolveThroughFrames(arg.Value, frames[:i])
		}
	}
	return name, true
}

func (s *typedefCycleScanner) recordEdge(to string, args []ast.TypeNode, guarded, hard bool, frames []typedefParamFrame) {
	forwarded := false
	expectedArgs := len(s.sourceParams)
	if len(args) == expectedArgs {
		if expectedArgs == 0 {
			forwarded = true
		} else {
			forwarded = true
			for i, arg := range args {
				publicConst, ok := arg.(*ast.PublicConstantNode)
				if !ok {
					forwarded = false
					break
				}
				finalName, ok := resolveThroughFrames(publicConst.Value, frames)
				if !ok || finalName != s.sourceParams[i] {
					forwarded = false
					break
				}
			}
		}
	}

	s.edges = append(s.edges, typedefCycleEdge{
		from:     s.source,
		to:       to,
		guarded:  guarded,
		hard:     hard,
		forwards: forwarded,
	})
}

// walk scans a type AST node collecting recursive edges. guarded indicates
// that the node is inside one of the four guard containers, hard indicates
// that the reference passes through any other type constructor and frames
// contains substitutions of inlined non recursive helper parameters.
func (s *typedefCycleScanner) walk(node ast.Node, guarded, hard bool, frames []typedefParamFrame, inlining map[string]struct{}) {
	if node == nil {
		return
	}

	switch n := node.(type) {
	case *ast.PublicConstantNode:
		if mapped := s.substituteParameter(n.Value, frames); mapped != nil {
			s.walk(mapped, guarded, hard, frames[:len(frames)-1], inlining)
			return
		}

		if name, ok := s.typedefNameOf(s.resolve(n)); ok {
			s.referenceTypedef(name, nil, guarded, hard, frames, inlining)
		}
	case *ast.PrivateConstantNode:
		if name, ok := s.typedefNameOf(s.resolve(n)); ok {
			s.referenceTypedef(name, nil, guarded, hard, frames, inlining)
		}
	case *ast.ConstantLookupNode:
		if name, ok := s.typedefNameOf(s.resolve(n)); ok {
			s.referenceTypedef(name, nil, guarded, hard, frames, inlining)
		}
	case *ast.GenericConstantNode:
		head := s.resolve(n.Constant)
		switch {
		case s.isGuardContainer(head):
			// references inside a guard container are protected
			for _, arg := range n.TypeArguments {
				s.walk(arg, true, hard, frames, inlining)
			}
		case isTypedefType(head):
			name := typedefName(head)
			s.referenceTypedef(name, n.TypeArguments, guarded, hard, frames, inlining)
		default:
			// any other generic type constructor hardens the whole subtree
			for _, arg := range n.TypeArguments {
				s.walkHard(arg, frames, inlining)
			}
		}
	case *ast.BinaryTypeNode:
		switch n.Op.Type {
		case token.OR:
			s.walk(n.Left, guarded, hard, frames, inlining)
			s.walk(n.Right, guarded, hard, frames, inlining)
		default:
			// intersections and other operators are not transparent
			s.walkHard(n.Left, frames, inlining)
			s.walkHard(n.Right, frames, inlining)
		}
	case *ast.UnionTypeNode:
		for _, element := range n.Elements {
			s.walk(element, guarded, hard, frames, inlining)
		}
	case *ast.NilableTypeNode:
		s.walk(n.TypeNode, guarded, hard, frames, inlining)
	default:
		// every other type constructor (callables, boxes, not, exact,
		// singleton, instance of, intersections, ...) hardens the subtree
		s.walkHardNode(n, frames, inlining)
	}
}

func (s *typedefCycleScanner) typedefNameOf(typ types.Type) (string, bool) {
	switch t := typ.(type) {
	case *types.NamedType:
		return t.Name, true
	case *types.GenericNamedType:
		return t.Name, true
	default:
		return "", false
	}
}

func (s *typedefCycleScanner) substituteParameter(name string, frames []typedefParamFrame) ast.TypeNode {
	for i := len(frames) - 1; i >= 0; i-- {
		frame := frames[i]
		for j, param := range frame.params {
			if param != name {
				continue
			}
			if j >= len(frame.args) {
				return nil
			}
			return frame.args[j]
		}
	}
	return nil
}

func (s *typedefCycleScanner) referenceTypedef(name string, args []ast.TypeNode, guarded, hard bool, frames []typedefParamFrame, inlining map[string]struct{}) {
	if _, ok := s.targets[name]; ok {
		s.recordEdge(name, args, guarded, hard, frames)
		return
	}

	info := s.c.typedefCycleInfo(name)
	if info == nil {
		return
	}

	if _, ok := inlining[name]; ok {
		// helper-only cycle, it gets validated on its own back edge
		return
	}

	frame := typedefParamFrame{
		params: info.params,
		args:   args,
	}
	inlining[name] = struct{}{}
	s.c.withTypeDefinitionScopes(info.entry, func() {
		s.walk(info.body, guarded, hard, append(frames, frame), inlining)
	})
	delete(inlining, name)
}

// walkHard continues the scan in a subtree where no transparent constructor
// can protect recursive references anymore.
func (s *typedefCycleScanner) walkHard(node ast.Node, frames []typedefParamFrame, inlining map[string]struct{}) {
	s.walk(node, true, true, frames, inlining)
}

// walkHardNode scans all type nodes below the given unsupported constructor
// marking every found recursive reference as hard.
func (s *typedefCycleScanner) walkHardNode(node ast.Node, frames []typedefParamFrame, inlining map[string]struct{}) {
	ast.Traverse(
		node,
		func(n, _ ast.Node) ast.TraverseOption {
			typeNode, ok := n.(ast.TypeNode)
			if !ok || n == node {
				return ast.TraverseContinue
			}
			s.walk(typeNode, true, true, frames, inlining)
			return ast.TraverseSkip
		},
		nil,
	)
}

func isTypedefType(typ types.Type) bool {
	switch typ.(type) {
	case *types.NamedType, *types.GenericNamedType:
		return true
	default:
		return false
	}
}

func typedefName(typ types.Type) string {
	switch t := typ.(type) {
	case *types.NamedType:
		return t.Name
	case *types.GenericNamedType:
		return t.Name
	default:
		return ""
	}
}

func typedefNameForCheck(check *typeDefinitionCheck) string {
	return typedefName(check.typ)
}

func isTypedefCheck(check *typeDefinitionCheck) bool {
	if check == nil || len(check.entries) == 0 {
		return false
	}
	for _, entry := range check.entries {
		switch entry.node.(type) {
		case *ast.TypeDefinitionNode, *ast.GenericTypeDefinitionNode:
		default:
			return false
		}
	}
	return true
}

// isLegallyRecursiveTypedef decides whether re-entering the currently checked
// typedef closes a legal recursive cycle. Class, mixin, interface and include
// cycles are never affected and keep their historic rejection behavior.
func (c *Checker) isLegallyRecursiveTypedef(check *typeDefinitionCheck, location *position.Location) bool {
	if !isTypedefCheck(check) {
		return false
	}

	name := typedefNameForCheck(check)
	if name == "" {
		return false
	}

	idx := -1
	for i := len(c.checkingTypedefs) - 1; i >= 0; i-- {
		if c.checkingTypedefs[i] == name {
			idx = i
			break
		}
	}
	if idx < 0 {
		return false
	}

	members := c.checkingTypedefs[idx:]
	return c.validateTypedefCycle(name, members)
}

// validateTypedefCycle validates the cycle closed by `target` whose members
// are currently being checked. Returns true when the cycle is legal.
func (c *Checker) validateTypedefCycle(target string, members []string) bool {
	memberSet := make(map[string]struct{}, len(members))
	for _, name := range members {
		memberSet[name] = struct{}{}
	}

	// all members must have the same type parameter count
	paramCount := -1
	for _, name := range members {
		info := c.typedefCycleInfo(name)
		if info == nil {
			return false
		}
		count := len(info.params)
		if paramCount == -1 {
			paramCount = count
		} else if paramCount != count {
			return false
		}
	}

	edges := c.collectTypedefCycleEdges(members)
	adjacency := make(map[string][]typedefCycleEdge)
	for _, edge := range edges {
		if _, ok := memberSet[edge.to]; !ok {
			continue
		}
		if edge.hard || !edge.forwards {
			return false
		}
		adjacency[edge.from] = append(adjacency[edge.from], edge)
	}

	// every cycle must pass through a guard container, hence the subgraph of
	// unguarded edges must be acyclic
	return !hasUnguardedCycle(members, adjacency)
}

// hasUnguardedCycle reports whether the graph of unguarded edges contains a
// cycle.
func hasUnguardedCycle(nodes []string, adjacency map[string][]typedefCycleEdge) bool {
	const (
		white = 0
		gray  = 1
		black = 2
	)
	colors := make(map[string]uint8)

	var visit func(name string) bool
	visit = func(name string) bool {
		colors[name] = gray
		for _, edge := range adjacency[name] {
			if edge.guarded {
				continue
			}
			switch colors[edge.to] {
			case gray:
				return true
			case white:
				if visit(edge.to) {
					return true
				}
			}
		}
		colors[name] = black
		return false
	}

	for _, name := range nodes {
		if colors[name] == white && visit(name) {
			return true
		}
	}
	return false
}
