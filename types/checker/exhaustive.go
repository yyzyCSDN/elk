// This file implements compile time exhaustiveness checking for the
// exhaustive `switch!` expression.
//
// The analysis works over symbolic value sets ("spaces") and never executes
// user code. It supports precisely the following reliable domain:
//
//   - nil, Bool and finite literal unions of Int, String and Symbol
//   - native ArrayList and ArrayTuple values nested at any depth
//   - union and nilable types built from the above
//
// Reliable (pure) patterns are bindings, literals, list and tuple patterns
// with at most one rest element at any position, `as`, nilable, must, `||`
// and `&&`. Every other pattern (dynamic values, object getters, regexes,
// ranges, relational patterns, constants, macros, map/record/set patterns...)
// may invoke user code and even mutate the structures reached from the
// matched value, so it can never contribute a reliable coverage proof.
package checker

import (
	"fmt"
	"strconv"

	"github.com/elk-language/elk/parser/ast"
	"github.com/elk-language/elk/token"
	"github.com/elk-language/elk/types"
	"github.com/elk-language/elk/value/symbol"
)

// A valSpace is a symbolic set of values sharing a static type.
type valSpace interface {
	spaceType() types.Type
}

// The empty set.
type emptySpace struct {
	typ types.Type
}

func (s *emptySpace) spaceType() types.Type {
	if s.typ == nil {
		return types.Never{}
	}
	return s.typ
}

// All values of the given type, except the literal singletons stored in
// forbidden. Only used for non enumerable class types such as Int.
type wildSpace struct {
	typ       types.Type
	forbidden []types.Type
}

func (s *wildSpace) spaceType() types.Type { return s.typ }

// A single literal value such as `nil`, `true`, `3`, `"foo"` or `:bar`.
type litSpace struct {
	typ types.Type
}

func (s *litSpace) spaceType() types.Type { return s.typ }

// A finite union of spaces.
type orSpace struct {
	typ     types.Type
	members []valSpace
}

func (s *orSpace) spaceType() types.Type { return s.typ }

// A set of ArrayList or ArrayTuple values described by length shapes.
type listSpace struct {
	typ      types.Type
	tuple    bool
	elemType types.Type
	shapes   []*listShape
}

func (s *listSpace) spaceType() types.Type { return s.typ }

// A listShape describes a family of list lengths.
//
// A closed shape covers exactly one length, its fixed element spaces being
// stored in prefix. An open shape covers every length L >= minLength:
// prefix elements are constrained from the start, suffix elements from the
// end and all middle elements by the middle space. minLength is always at
// least len(prefix) + len(suffix) and lets a residual shape start covering
// only beyond the lengths that were reasoned about explicitly.
type listShape struct {
	open      bool
	minLength int
	prefix    []valSpace
	suffix    []valSpace
	middle    valSpace
}

func (s *listShape) fixedCount() int {
	return len(s.prefix) + len(s.suffix)
}

func newOpenListShape(prefix, suffix []valSpace, middle valSpace, minLength int) *listShape {
	if minLength < len(prefix)+len(suffix) {
		minLength = len(prefix) + len(suffix)
	}
	return &listShape{
		open:      true,
		minLength: minLength,
		prefix:    prefix,
		suffix:    suffix,
		middle:    middle,
	}
}

// Performs exhaustiveness reasoning for a single matched value type.
type exhaustiveness struct {
	c           *Checker
	matchedType types.Type
}

func (e *exhaustiveness) newEmpty(typ types.Type) valSpace {
	return &emptySpace{typ: typ}
}

// ---------------------------------------------------------------------------
// Type classification and top space construction
// ---------------------------------------------------------------------------

func (e *exhaustiveness) isArrayListClass(t types.Type) bool {
	g, ok := t.(*types.Generic)
	if !ok {
		return false
	}
	class, ok := g.Namespace.(*types.Class)
	return ok && class == e.c.StdArrayList()
}

func (e *exhaustiveness) isArrayTupleClass(t types.Type) bool {
	g, ok := t.(*types.Generic)
	if !ok {
		return false
	}
	class, ok := g.Namespace.(*types.Class)
	return ok && class == e.c.StdArrayTuple()
}

// Build the space containing every value of the given static type.
func (e *exhaustiveness) topSpace(typ types.Type) valSpace {
	switch t := typ.(type) {
	case types.Never:
		return e.newEmpty(typ)
	case types.Untyped:
		return e.newEmpty(typ)
	case types.Nil, types.True, types.False:
		return &litSpace{typ: t}
	case *types.IntLiteral, *types.Int64Literal, *types.Int32Literal, *types.Int16Literal, *types.Int8Literal,
		*types.UIntLiteral, *types.UInt64Literal, *types.UInt32Literal, *types.UInt16Literal, *types.UInt8Literal,
		*types.StringLiteral, *types.SymbolLiteral:
		return &litSpace{typ: t}
	case types.Bool:
		return e.union(&litSpace{typ: types.True{}}, &litSpace{typ: types.False{}})
	case *types.Union:
		members := make([]valSpace, 0, len(t.Elements))
		for _, element := range t.Elements {
			members = append(members, e.topSpace(element))
		}
		return e.unionOf(typ, members...)
	case *types.Nilable:
		return e.unionOf(typ, e.topSpace(t.Type), &litSpace{typ: types.Nil{}})
	case *types.NamedType:
		return e.topSpace(t.Type)
	case *types.Intersection:
		var result valSpace
		for _, element := range t.Elements {
			if result == nil {
				result = e.topSpace(element)
				continue
			}
			result = e.intersect(result, e.topSpace(element))
		}
		if result == nil {
			return &wildSpace{typ: typ}
		}
		return result
	case *types.Generic:
		if e.isArrayListClass(typ) || e.isArrayTupleClass(typ) {
			var elemType types.Type = types.Any{}
			if t.TypeArguments != nil && t.TypeArguments.Len() > 0 {
				elemType = t.Get(0).Type
			}
			return &listSpace{
				typ:      typ,
				tuple:    e.isArrayTupleClass(typ),
				elemType: elemType,
				shapes: []*listShape{
					newOpenListShape(nil, nil, e.topSpace(elemType), 0),
				},
			}
		}
		return &wildSpace{typ: typ}
	case *types.Class:
		// Bool is a finite enumerable domain even when referenced as a class.
		if t == e.c.StdBool() {
			return e.union(&litSpace{typ: types.True{}}, &litSpace{typ: types.False{}})
		}
		return &wildSpace{typ: typ}
	default:
		return &wildSpace{typ: typ}
	}
}

// ---------------------------------------------------------------------------
// Union
// ---------------------------------------------------------------------------

func (e *exhaustiveness) unionOf(typ types.Type, members ...valSpace) valSpace {
	var result valSpace
	for _, member := range members {
		if result == nil {
			result = member
			continue
		}
		result = e.union(result, member)
	}
	if result == nil {
		return e.newEmpty(typ)
	}
	return result
}

func flattenOr(s valSpace) []valSpace {
	if o, ok := s.(*orSpace); ok {
		return o.members
	}
	return []valSpace{s}
}

func (e *exhaustiveness) union(a, b valSpace) valSpace {
	if e.isEmpty(a) {
		return b
	}
	if e.isEmpty(b) {
		return a
	}

	members := append(flattenOr(a), flattenOr(b)...)
	var lits []*litSpace
	var wilds []*wildSpace
	var lists []*listSpace
	var others []valSpace

	for _, member := range members {
		switch m := member.(type) {
		case *litSpace:
			lits = append(lits, m)
		case *wildSpace:
			wilds = append(wilds, m)
		case *listSpace:
			lists = append(lists, m)
		default:
			others = append(others, m)
		}
	}

	var result []valSpace

	// Merge wildcard spaces of the same base class.
	mergedWilds := make([]*wildSpace, 0, len(wilds))
	for _, w := range wilds {
		merged := false
		for _, existing := range mergedWilds {
			if e.c.IsTheSameType(existing.typ, w.typ) {
				existing.forbidden = append(existing.forbidden, w.forbidden...)
				merged = true
				break
			}
		}
		if !merged {
			mergedWilds = append(mergedWilds, &wildSpace{
				typ:       w.typ,
				forbidden: append([]types.Type(nil), w.forbidden...),
			})
		}
	}

	// Deduplicate literals and drop the ones covered by a wildcard.
	for _, lit := range lits {
		duplicate := false
		for _, existing := range result {
			if el, ok := existing.(*litSpace); ok && e.c.IsTheSameType(el.typ, lit.typ) {
				duplicate = true
				break
			}
		}
		if duplicate {
			continue
		}
		coveredByWild := false
		for _, w := range mergedWilds {
			if e.c.TypesIntersect(w.typ, lit.typ) && !w.isForbidden(lit.typ, e) {
				coveredByWild = true
				break
			}
		}
		if !coveredByWild {
			result = append(result, lit)
		}
	}
	for _, w := range mergedWilds {
		result = append(result, w)
	}

	// Merge list spaces of the same collection type.
	mergedLists := make([]*listSpace, 0, len(lists))
	for _, list := range lists {
		merged := false
		for _, existing := range mergedLists {
			if existing.tuple == list.tuple && e.c.IsTheSameType(existing.typ, list.typ) {
				existing.shapes = e.mergeShapes(existing.shapes, list.shapes)
				merged = true
				break
			}
		}
		if !merged {
			copied := &listSpace{
				typ:      list.typ,
				tuple:    list.tuple,
				elemType: list.elemType,
				shapes:   append([]*listShape(nil), list.shapes...),
			}
			mergedLists = append(mergedLists, copied)
		}
	}
	for _, list := range mergedLists {
		result = append(result, list)
	}
	result = append(result, others...)

	if len(result) == 0 {
		return e.newEmpty(e.c.NewNormalisedUnion(a.spaceType(), b.spaceType()))
	}
	if len(result) == 1 {
		return result[0]
	}
	memberTypes := make([]types.Type, len(result))
	for i, member := range result {
		memberTypes[i] = member.spaceType()
	}
	return &orSpace{
		typ:     e.c.NewNormalisedUnion(memberTypes...),
		members: result,
	}
}

func (w *wildSpace) isForbidden(lit types.Type, e *exhaustiveness) bool {
	for _, f := range w.forbidden {
		if e.c.IsTheSameType(f, lit) {
			return true
		}
	}
	return false
}

func (e *exhaustiveness) mergeShapes(a, b []*listShape) []*listShape {
	result := append([]*listShape(nil), a...)
	for _, shape := range b {
		duplicate := false
		for _, existing := range result {
			if e.shapesEqual(existing, shape) {
				duplicate = true
				break
			}
		}
		if !duplicate {
			result = append(result, shape)
		}
	}
	return result
}

func (e *exhaustiveness) shapesEqual(a, b *listShape) bool {
	if a.open != b.open || a.fixedCount() != b.fixedCount() || a.minLength != b.minLength {
		return false
	}
	if len(a.prefix) != len(b.prefix) || len(a.suffix) != len(b.suffix) {
		return false
	}
	for i := range a.prefix {
		if !e.spacesEqual(a.prefix[i], b.prefix[i]) {
			return false
		}
	}
	for i := range a.suffix {
		if !e.spacesEqual(a.suffix[i], b.suffix[i]) {
			return false
		}
	}
	if a.open {
		return e.spacesEqual(a.middle, b.middle)
	}
	return true
}

func (e *exhaustiveness) spacesEqual(a, b valSpace) bool {
	if e.isEmpty(a) {
		return e.isEmpty(b)
	}
	switch at := a.(type) {
	case *litSpace:
		bt, ok := b.(*litSpace)
		return ok && e.c.IsTheSameType(at.typ, bt.typ)
	case *wildSpace:
		bt, ok := b.(*wildSpace)
		return ok && e.c.IsTheSameType(at.typ, bt.typ)
	case *orSpace:
		bt, ok := b.(*orSpace)
		if !ok || len(at.members) != len(bt.members) {
			return false
		}
		for i := range at.members {
			if !e.spacesEqual(at.members[i], bt.members[i]) {
				return false
			}
		}
		return true
	case *listSpace:
		bt, ok := b.(*listSpace)
		if !ok || at.tuple != bt.tuple || len(at.shapes) != len(bt.shapes) {
			return false
		}
		for i := range at.shapes {
			if !e.shapesEqual(at.shapes[i], bt.shapes[i]) {
				return false
			}
		}
		return true
	}
	return false
}

// ---------------------------------------------------------------------------
// Intersection
// ---------------------------------------------------------------------------

func (e *exhaustiveness) intersect(a, b valSpace) valSpace {
	if e.isEmpty(a) || e.isEmpty(b) {
		return e.newEmpty(e.c.NewNormalisedUnion(nonNeverType(a), nonNeverType(b)))
	}
	if o, ok := a.(*orSpace); ok {
		members := make([]valSpace, len(o.members))
		for i, member := range o.members {
			members[i] = e.intersect(member, b)
		}
		return e.unionOf(o.typ, members...)
	}
	if o, ok := b.(*orSpace); ok {
		members := make([]valSpace, len(o.members))
		for i, member := range o.members {
			members[i] = e.intersect(a, member)
		}
		return e.unionOf(o.typ, members...)
	}

	switch at := a.(type) {
	case *litSpace:
		bt, ok := b.(*litSpace)
		if ok {
			if e.c.IsTheSameType(at.typ, bt.typ) {
				return at
			}
			return e.newEmpty(at.typ)
		}
		bw, ok := b.(*wildSpace)
		if ok {
			if e.c.TypesIntersect(at.typ, bw.typ) && !bw.isForbidden(at.typ, e) {
				return at
			}
			return e.newEmpty(at.typ)
		}
		if e.c.TypesIntersect(a.spaceType(), b.spaceType()) {
			return a
		}
		return e.newEmpty(at.typ)
	case *wildSpace:
		switch bt := b.(type) {
		case *wildSpace:
			if !e.c.TypesIntersect(at.typ, bt.typ) {
				return e.newEmpty(at.typ)
			}
			if e.c.isSubtype(at.typ, bt.typ, nil) {
				return &wildSpace{typ: at.typ, forbidden: append(append([]types.Type(nil), at.forbidden...), bt.forbidden...)}
			}
			if e.c.isSubtype(bt.typ, at.typ, nil) {
				return &wildSpace{typ: bt.typ, forbidden: append(append([]types.Type(nil), bt.forbidden...), at.forbidden...)}
			}
			return &wildSpace{typ: at.typ, forbidden: append([]types.Type(nil), at.forbidden...)}
		case *listSpace:
			if e.c.TypesIntersect(at.typ, bt.typ) {
				return bt
			}
			return e.newEmpty(bt.typ)
		}
	case *listSpace:
		switch bt := b.(type) {
		case *listSpace:
			return e.intersectLists(at, bt)
		case *wildSpace:
			if e.c.TypesIntersect(at.typ, bt.typ) {
				return at
			}
			return e.newEmpty(at.typ)
		}
	}

	if e.c.TypesIntersect(a.spaceType(), b.spaceType()) {
		return a
	}
	return e.newEmpty(a.spaceType())
}

func nonNeverType(s valSpace) types.Type {
	if e, ok := s.(*emptySpace); ok && e.typ != nil {
		return e.typ
	}
	return s.spaceType()
}

// ---------------------------------------------------------------------------
// Subtraction
// ---------------------------------------------------------------------------

func (e *exhaustiveness) subtract(a, b valSpace) valSpace {
	if e.isEmpty(a) || e.isEmpty(b) {
		return a
	}
	if o, ok := b.(*orSpace); ok {
		result := a
		for _, member := range o.members {
			result = e.subtract(result, member)
		}
		return result
	}
	if o, ok := a.(*orSpace); ok {
		members := make([]valSpace, len(o.members))
		for i, member := range o.members {
			members[i] = e.subtract(member, b)
		}
		return e.unionOf(o.typ, members...)
	}

	switch at := a.(type) {
	case *litSpace:
		switch bt := b.(type) {
		case *litSpace:
			if e.c.IsTheSameType(at.typ, bt.typ) {
				return e.newEmpty(at.typ)
			}
			return at
		case *wildSpace:
			if e.c.TypesIntersect(at.typ, bt.typ) {
				return e.newEmpty(at.typ)
			}
			return at
		}
	case *wildSpace:
		switch bt := b.(type) {
		case *litSpace:
			if e.c.TypesIntersect(at.typ, bt.typ) {
				if at.isForbidden(bt.typ, e) {
					return at
				}
				return &wildSpace{
					typ:       at.typ,
					forbidden: append(append([]types.Type(nil), at.forbidden...), bt.typ),
				}
			}
			return at
		case *wildSpace:
			if !e.c.TypesIntersect(at.typ, bt.typ) {
				return at
			}
			if e.c.isSubtype(at.typ, bt.typ, nil) {
				return e.newEmpty(at.typ)
			}
			return at
		}
	case *listSpace:
		if bt, ok := b.(*listSpace); ok {
			return e.subtractLists(at, bt)
		}
	}

	if e.c.TypesIntersect(a.spaceType(), b.spaceType()) {
		// Cannot reason about this combination, keep the whole space to
		// stay sound (exhaustiveness may not be provable, but is never assumed).
		return a
	}
	return a
}

// ---------------------------------------------------------------------------
// List shape algebra
// ---------------------------------------------------------------------------

// Project a shape onto the constraints of an exact length.
// The boolean result is false when the shape does not cover the given
// length. An empty slice with a true result means a covered length of
// zero and must not be confused with lack of coverage.
func (e *exhaustiveness) projectShape(shape *listShape, length int) ([]valSpace, bool) {
	if !shape.open {
		if length != len(shape.prefix) {
			return nil, false
		}
		return append([]valSpace(nil), shape.prefix...), true
	}

	fixed := shape.fixedCount()
	if length < shape.minLength {
		return nil, false
	}

	result := make([]valSpace, 0, length)
	result = append(result, shape.prefix...)
	for i := fixed; i < length; i++ {
		result = append(result, shape.middle)
	}
	result = append(result, shape.suffix...)
	return result, true
}

// Union of constraints of all shapes covering the given length.
func (e *exhaustiveness) projectShapes(shapes []*listShape, length int) ([]valSpace, bool) {
	var result []valSpace
	covered := false
	for _, shape := range shapes {
		projected, ok := e.projectShape(shape, length)
		if !ok {
			continue
		}
		covered = true
		if result == nil {
			result = projected
			continue
		}
		for i := range result {
			result[i] = e.union(result[i], projected[i])
		}
	}
	return result, covered
}

func (e *exhaustiveness) maxFixedCount(shapes ...[]*listShape) int {
	maxFixed := 0
	for _, group := range shapes {
		for _, shape := range group {
			if fixed := shape.fixedCount(); fixed > maxFixed {
				maxFixed = fixed
			}
		}
	}
	return maxFixed
}

func (e *exhaustiveness) subtractLists(a, b *listSpace) valSpace {
	bound := e.maxFixedCount(a.shapes, b.shapes)
	var resultShapes []*listShape

	for length := 0; length <= bound; length++ {
		va, aCovered := e.projectShapes(a.shapes, length)
		if !aCovered {
			continue
		}
		vb, bCovered := e.projectShapes(b.shapes, length)
		if !bCovered {
			resultShapes = append(resultShapes, &listShape{prefix: va})
			continue
		}

		residual := make([]valSpace, length)
		anyLeft := false
		for i := range va {
			residual[i] = e.subtract(va[i], vb[i])
			if !e.isEmpty(residual[i]) {
				anyLeft = true
			}
		}
		// A fully covered length (including length zero, which has no
		// positions at all) must not leave any residual shape behind.
		if anyLeft {
			resultShapes = append(resultShapes, &listShape{prefix: residual})
		}
	}

	if openShapes := e.subtractOpenShapes(a.shapes, b.shapes, bound); len(openShapes) > 0 {
		resultShapes = append(resultShapes, openShapes...)
	}

	if len(resultShapes) == 0 {
		return e.newEmpty(a.typ)
	}
	return &listSpace{
		typ:      a.typ,
		tuple:    a.tuple,
		elemType: a.elemType,
		shapes:   resultShapes,
	}
}

func (e *exhaustiveness) intersectLists(a, b *listSpace) valSpace {
	bound := e.maxFixedCount(a.shapes, b.shapes)
	var resultShapes []*listShape

	for length := 0; length <= bound; length++ {
		va, aCovered := e.projectShapes(a.shapes, length)
		vb, bCovered := e.projectShapes(b.shapes, length)
		if !aCovered || !bCovered {
			continue
		}

		residual := make([]valSpace, length)
		emptyPosition := false
		for i := range va {
			residual[i] = e.intersect(va[i], vb[i])
			if e.isEmpty(residual[i]) {
				emptyPosition = true
			}
		}
		if !emptyPosition {
			resultShapes = append(resultShapes, &listShape{prefix: residual})
		}
	}

	if openShapes := e.intersectOpenShapes(a.shapes, b.shapes, bound); len(openShapes) > 0 {
		resultShapes = append(resultShapes, openShapes...)
	}

	if len(resultShapes) == 0 {
		return e.newEmpty(a.typ)
	}
	return &listSpace{
		typ:      a.typ,
		tuple:    a.tuple,
		elemType: a.elemType,
		shapes:   resultShapes,
	}
}

func openShapes(shapes []*listShape) []*listShape {
	var result []*listShape
	for _, shape := range shapes {
		if shape.open {
			result = append(result, shape)
		}
	}
	return result
}

// Constraint of open shapes at prefix position i.
func (e *exhaustiveness) openPrefixConstraint(shapes []*listShape, i int) valSpace {
	var result valSpace
	for _, shape := range shapes {
		var constraint valSpace
		if i < len(shape.prefix) {
			constraint = shape.prefix[i]
		} else {
			constraint = shape.middle
		}
		if result == nil {
			result = constraint
		} else {
			result = e.union(result, constraint)
		}
	}
	return result
}

// Constraint of open shapes at suffix position j, counted from the end.
func (e *exhaustiveness) openSuffixConstraint(shapes []*listShape, j int) valSpace {
	var result valSpace
	for _, shape := range shapes {
		var constraint valSpace
		if j < len(shape.suffix) {
			constraint = shape.suffix[len(shape.suffix)-1-j]
		} else {
			constraint = shape.middle
		}
		if result == nil {
			result = constraint
		} else {
			result = e.union(result, constraint)
		}
	}
	return result
}

func (e *exhaustiveness) openMiddle(shapes []*listShape) valSpace {
	var result valSpace
	for _, shape := range shapes {
		if result == nil {
			result = shape.middle
		} else {
			result = e.union(result, shape.middle)
		}
	}
	return result
}

// Build the residual open shapes covering every length greater than bound.
func (e *exhaustiveness) subtractOpenShapes(a, b []*listShape, bound int) []*listShape {
	aOpen := openShapes(a)
	if len(aOpen) == 0 {
		return nil
	}
	bOpen := openShapes(b)
	if len(bOpen) == 0 {
		// b only contains closed shapes, they cannot cover lengths beyond
		// the bound, so every open shape of a survives past the bound.
		result := make([]*listShape, 0, len(aOpen))
		for _, shape := range aOpen {
			result = append(result, newOpenListShape(
				shape.prefix,
				shape.suffix,
				shape.middle,
				bound+1,
			))
		}
		return result
	}

	prefixCount := 0
	suffixCount := 0
	for _, shape := range append(append([]*listShape(nil), aOpen...), bOpen...) {
		if len(shape.prefix) > prefixCount {
			prefixCount = len(shape.prefix)
		}
		if len(shape.suffix) > suffixCount {
			suffixCount = len(shape.suffix)
		}
	}

	prefix := make([]valSpace, prefixCount)
	for i := range prefix {
		ca := e.openPrefixConstraint(aOpen, i)
		cb := e.openPrefixConstraint(bOpen, i)
		prefix[i] = e.subtract(ca, cb)
		if e.isEmpty(prefix[i]) {
			return nil
		}
	}

	suffix := make([]valSpace, suffixCount)
	for j := range suffix {
		ca := e.openSuffixConstraint(aOpen, j)
		cb := e.openSuffixConstraint(bOpen, j)
		suffix[j] = e.subtract(ca, cb)
		if e.isEmpty(suffix[j]) {
			return nil
		}
	}

	middle := e.subtract(e.openMiddle(aOpen), e.openMiddle(bOpen))
	if e.isEmpty(middle) {
		return nil
	}

	return []*listShape{newOpenListShape(prefix, suffix, middle, bound+1)}
}

func (e *exhaustiveness) intersectOpenShapes(a, b []*listShape, bound int) []*listShape {
	aOpen := openShapes(a)
	bOpen := openShapes(b)
	if len(aOpen) == 0 || len(bOpen) == 0 {
		return nil
	}

	prefixCount := 0
	suffixCount := 0
	for _, shape := range append(append([]*listShape(nil), aOpen...), bOpen...) {
		if len(shape.prefix) > prefixCount {
			prefixCount = len(shape.prefix)
		}
		if len(shape.suffix) > suffixCount {
			suffixCount = len(shape.suffix)
		}
	}

	prefix := make([]valSpace, prefixCount)
	for i := range prefix {
		prefix[i] = e.intersect(e.openPrefixConstraint(aOpen, i), e.openPrefixConstraint(bOpen, i))
		if e.isEmpty(prefix[i]) {
			return nil
		}
	}

	suffix := make([]valSpace, suffixCount)
	for j := range suffix {
		suffix[j] = e.intersect(e.openSuffixConstraint(aOpen, j), e.openSuffixConstraint(bOpen, j))
		if e.isEmpty(suffix[j]) {
			return nil
		}
	}

	middle := e.intersect(e.openMiddle(aOpen), e.openMiddle(bOpen))
	if e.isEmpty(middle) {
		return nil
	}

	return []*listShape{newOpenListShape(prefix, suffix, middle, bound+1)}
}

// ---------------------------------------------------------------------------
// Emptiness
// ---------------------------------------------------------------------------

func (e *exhaustiveness) isEmpty(s valSpace) bool {
	switch t := s.(type) {
	case *emptySpace:
		return true
	case *litSpace, *wildSpace:
		return false
	case *orSpace:
		for _, member := range t.members {
			if !e.isEmpty(member) {
				return false
			}
		}
		return true
	case *listSpace:
		for _, shape := range t.shapes {
			if !e.shapeIsEmpty(shape) {
				return false
			}
		}
		return true
	}
	return true
}

func (e *exhaustiveness) shapeIsEmpty(shape *listShape) bool {
	for _, s := range shape.prefix {
		if e.isEmpty(s) {
			return true
		}
	}
	for _, s := range shape.suffix {
		if e.isEmpty(s) {
			return true
		}
	}
	if shape.open && e.isEmpty(shape.middle) {
		return true
	}
	return false
}

// Keep only immutable scalar singleton facts. List content facts depend on
// mutable structures and are dropped on purpose.
func (e *exhaustiveness) scalarPart(s valSpace) valSpace {
	switch t := s.(type) {
	case *litSpace:
		return t
	case *orSpace:
		members := make([]valSpace, 0, len(t.members))
		for _, member := range t.members {
			if scalar := e.scalarPart(member); !e.isEmpty(scalar) {
				members = append(members, scalar)
			}
		}
		return e.unionOf(t.typ, members...)
	default:
		return e.newEmpty(s.spaceType())
	}
}

// ---------------------------------------------------------------------------
// Pattern to space translation
// ---------------------------------------------------------------------------

// Translate a checked pattern node into its covered value space.
// expected is the static type of the position the pattern matches against.
// The second result is false when the pattern invokes user code and cannot
// be used as a reliable coverage proof. The returned space still contains
// the subset that can be proven reliably (eg. the nil branch of a nilable
// pattern wrapping an impure pattern).
func (e *exhaustiveness) patternSpace(pattern ast.PatternNode, expected types.Type) (valSpace, bool) {
	switch n := pattern.(type) {
	case *ast.PublicIdentifierNode, *ast.PrivateIdentifierNode:
		return e.topSpace(expected), true
	case *ast.NilLiteralNode:
		return &litSpace{typ: types.Nil{}}, true
	case *ast.TrueLiteralNode:
		return &litSpace{typ: types.True{}}, true
	case *ast.FalseLiteralNode:
		return &litSpace{typ: types.False{}}, true
	case *ast.IntLiteralNode, *ast.Int64LiteralNode, *ast.Int32LiteralNode, *ast.Int16LiteralNode, *ast.Int8LiteralNode,
		*ast.UIntLiteralNode, *ast.UInt64LiteralNode, *ast.UInt32LiteralNode, *ast.UInt16LiteralNode, *ast.UInt8LiteralNode,
		*ast.DoubleQuotedStringLiteralNode, *ast.RawStringLiteralNode, *ast.SimpleSymbolLiteralNode:
		return &litSpace{typ: e.c.TypeOf(n)}, true
	case *ast.UnaryExpressionNode:
		// Signed numeric literals such as `-3`.
		if (n.Op.Type == token.MINUS || n.Op.Type == token.PLUS) && e.c.TypeOf(n).IsLiteral() {
			return &litSpace{typ: e.c.TypeOf(n)}, true
		}
		return e.newEmpty(expected), false
	case *ast.AsPatternNode:
		return e.patternSpace(n.Pattern, expected)
	case *ast.NilablePatternNode:
		inner, pure := e.patternSpace(n.Pattern, expected)
		nilSpace := &litSpace{typ: types.Nil{}}
		if pure {
			return e.union(nilSpace, inner), true
		}
		return nilSpace, false
	case *ast.MustPatternNode:
		return e.subtract(e.topSpace(expected), &litSpace{typ: types.Nil{}}), true
	case *ast.BinaryPatternNode:
		left, leftPure := e.patternSpace(n.Left, expected)
		right, rightPure := e.patternSpace(n.Right, expected)
		switch n.Op.Type {
		case token.OR_OR:
			space := e.union(left, right)
			return space, leftPure && rightPure
		case token.AND_AND:
			space := e.intersect(left, right)
			return space, leftPure && rightPure
		default:
			return e.newEmpty(expected), false
		}
	case *ast.ListPatternNode:
		return e.collectionPatternSpace(n.Elements, n.ElementType, e.c.TypeOf(n), false)
	case *ast.TuplePatternNode:
		return e.collectionPatternSpace(n.Elements, n.ElementType, e.c.TypeOf(n), true)
	default:
		// Dynamic values, constants, regexes, ranges, relational patterns,
		// object getters, map/record/set patterns, macros and any other
		// pattern invoking user code are not reliable coverage proofs.
		return e.newEmpty(expected), false
	}
}

func (e *exhaustiveness) collectionPatternSpace(elements []ast.PatternNode, elemType, collectionType types.Type, tuple bool) (valSpace, bool) {
	restIndex := -1
	for i, element := range elements {
		if _, ok := element.(*ast.RestPatternNode); ok {
			if restIndex != -1 {
				// Multiple rest elements cannot be reasoned about.
				return e.newEmpty(collectionType), false
			}
			restIndex = i
		}
	}

	elementTop := e.topSpace(elemType)

	if restIndex == -1 {
		prefix := make([]valSpace, len(elements))
		for i, element := range elements {
			space, pure := e.patternSpace(element, elemType)
			if !pure {
				return e.newEmpty(collectionType), false
			}
			prefix[i] = space
		}
		return &listSpace{
			typ:      collectionType,
			tuple:    tuple,
			elemType: elemType,
			shapes:   []*listShape{{prefix: prefix}},
		}, true
	}

	prefixPatterns := elements[:restIndex]
	suffixPatterns := elements[restIndex+1:]

	prefix := make([]valSpace, len(prefixPatterns))
	for i, element := range prefixPatterns {
		space, pure := e.patternSpace(element, elemType)
		if !pure {
			return e.newEmpty(collectionType), false
		}
		prefix[i] = space
	}

	suffix := make([]valSpace, len(suffixPatterns))
	for i, element := range suffixPatterns {
		space, pure := e.patternSpace(element, elemType)
		if !pure {
			return e.newEmpty(collectionType), false
		}
		suffix[i] = space
	}

	return &listSpace{
		typ:      collectionType,
		tuple:    tuple,
		elemType: elemType,
		shapes: []*listShape{
			newOpenListShape(prefix, suffix, elementTop, len(prefix)+len(suffix)),
		},
	}, true
}

// ---------------------------------------------------------------------------
// Branch analysis
// ---------------------------------------------------------------------------

const unreachableBranchWarning = "this branch is unreachable, all values it can match are already covered by earlier branches"

const dynamicExhaustivenessFailure = "cannot prove exhaustiveness of this `switch!` expression: a branch uses a dynamic pattern that may invoke user code and mutate the matched value; add a pure catch-all branch or an `else` branch"

// Analyze every branch in order and emit diagnostics.
// Returns true when the switch is proven exhaustive.
func (e *exhaustiveness) analyze(node *ast.SwitchExpressionNode) bool {
	top := e.topSpace(e.matchedType)
	remaining := top
	coveredScalars := e.newEmpty(types.Never{})
	sawImpure := false

	for _, caseNode := range node.Cases {
		rawSpace, pure := e.patternSpace(caseNode.Pattern, e.matchedType)
		space := e.intersect(rawSpace, top)

		if pure {
			if !e.isEmpty(space) && e.isEmpty(e.intersect(remaining, space)) {
				e.c.addWarning(unreachableBranchWarning, caseNode.Location())
			}
			if !e.isEmpty(space) {
				remaining = e.subtract(remaining, space)
			}
			coveredScalars = e.union(coveredScalars, e.scalarPart(space))
			continue
		}

		// An impure pattern may invoke arbitrary user code and mutate the
		// structures reached by the matched value. All coverage facts that
		// depend on mutable content are therefore invalidated; only
		// immutable scalar singleton facts survive.
		sawImpure = true
		coveredScalars = e.union(coveredScalars, e.scalarPart(space))
		remaining = e.subtract(top, coveredScalars)
	}

	if len(node.ElseBody) > 0 {
		return true
	}
	if e.isEmpty(remaining) {
		return true
	}

	if sawImpure {
		e.c.addFailure(dynamicExhaustivenessFailure, node.Location())
		return false
	}

	witness, ok := e.witness(remaining)
	if !ok {
		e.c.addFailure(dynamicExhaustivenessFailure, node.Location())
		return false
	}

	e.c.addFailure(
		fmt.Sprintf("non-exhaustive `switch!` expression, no branch matches the value %s", witness),
		node.Location(),
	)
	return false
}

// ---------------------------------------------------------------------------
// Witness generation
// ---------------------------------------------------------------------------

// Build a concrete value of the space rendered as Elk source code.
// Returns ok=false when no concrete value can be constructed without
// guessing, in which case no value must be fabricated.
func (e *exhaustiveness) witness(s valSpace) (string, bool) {
	switch t := s.(type) {
	case *emptySpace:
		return "", false
	case *litSpace:
		return types.Inspect(t.typ), true
	case *wildSpace:
		return e.wildWitness(t)
	case *orSpace:
		for _, member := range t.members {
			if value, ok := e.witness(member); ok {
				return value, true
			}
		}
		return "", false
	case *listSpace:
		return e.listWitness(t)
	}
	return "", false
}

func (e *exhaustiveness) wildWitness(w *wildSpace) (string, bool) {
	switch {
	case e.c.IsTheSameType(w.typ, e.c.StdBool()):
		trueLit := types.True{}
		if !w.isForbidden(trueLit, e) {
			return types.Inspect(trueLit), true
		}
		falseLit := types.False{}
		if !w.isForbidden(falseLit, e) {
			return types.Inspect(falseLit), true
		}
		return "", false
	case e.c.isSubtype(w.typ, e.c.StdAnyInt(), nil):
		for i := 0; i < 10000; i++ {
			lit := types.NewIntLiteral(strconv.Itoa(i))
			if !w.isForbidden(lit, e) {
				return types.Inspect(lit), true
			}
		}
		return "", false
	case e.c.isSubtype(w.typ, e.c.Std(symbol.C_String), nil):
		for _, value := range []string{"", "a", "b", "c", "d", "e"} {
			lit := types.NewStringLiteral(value)
			if !w.isForbidden(lit, e) {
				return types.Inspect(lit), true
			}
		}
		for i := 0; i < 10000; i++ {
			lit := types.NewStringLiteral("value" + strconv.Itoa(i))
			if !w.isForbidden(lit, e) {
				return types.Inspect(lit), true
			}
		}
		return "", false
	case e.c.isSubtype(w.typ, e.c.Std(symbol.C_Symbol), nil):
		for _, value := range []string{"a", "b", "c", "d", "e"} {
			lit := types.NewSymbolLiteral(value)
			if !w.isForbidden(lit, e) {
				return types.Inspect(lit), true
			}
		}
		for i := 0; i < 10000; i++ {
			lit := types.NewSymbolLiteral("symbol" + strconv.Itoa(i))
			if !w.isForbidden(lit, e) {
				return types.Inspect(lit), true
			}
		}
		return "", false
	default:
		return "", false
	}
}

func (e *exhaustiveness) listWitness(list *listSpace) (string, bool) {
	type candidate struct {
		length int
		vector []valSpace
	}

	var candidates []candidate
	for _, shape := range list.shapes {
		if e.shapeIsEmpty(shape) {
			continue
		}
		if !shape.open {
			candidates = append(candidates, candidate{
				length: len(shape.prefix),
				vector: shape.prefix,
			})
			continue
		}
		// Open shape: use its shortest possible length. Middle positions
		// are padded with witnesses of the middle space.
		vector := append([]valSpace(nil), shape.prefix...)
		for i := shape.fixedCount(); i < shape.minLength; i++ {
			vector = append(vector, shape.middle)
		}
		vector = append(vector, shape.suffix...)
		candidates = append(candidates, candidate{
			length: shape.minLength,
			vector: vector,
		})
	}

	if len(candidates) == 0 {
		return "", false
	}

	// Prefer the shortest concrete value.
	best := candidates[0]
	for _, candidate := range candidates[1:] {
		if candidate.length < best.length {
			best = candidate
		}
	}

	parts := make([]string, len(best.vector))
	for i, element := range best.vector {
		value, ok := e.witness(element)
		if !ok {
			return "", false
		}
		parts[i] = value
	}

	rendered := "[" + joinStrings(parts, ", ") + "]"
	if list.tuple {
		rendered = "%[" + joinStrings(parts, ", ") + "]"
	}
	return rendered, true
}

func joinStrings(parts []string, separator string) string {
	result := ""
	for i, part := range parts {
		if i != 0 {
			result += separator
		}
		result += part
	}
	return result
}
