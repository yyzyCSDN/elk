package checker

import (
	"github.com/elk-language/elk/types"
)

// This file contains the runtime side of transparent recursive typedefs:
// interning of generic recursive instances, transparent unfolding and the
// coinductive assumption stacks used to subtype check cyclic type graphs
// without expanding them to any fixed depth.

type subtypePair struct {
	a types.Type
	b types.Type
}

type intersectPair struct {
	a types.Type
	b types.Type
}

func typeSlicesEqual(a, b []types.Type) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

// internRecursiveGeneric returns the unique transparent instance of the given
// recursive generic typedef for the given arguments. The instance is
// registered before its body is built, which keeps the produced type graph
// cyclic instead of infinitely expanded.
func (c *Checker) internRecursiveGeneric(def *types.GenericNamedType, args []types.Type) *types.RecursiveGeneric {
	if c.recursiveGenericCache == nil {
		c.recursiveGenericCache = make(map[*types.GenericNamedType][]*types.RecursiveGeneric)
	}

	for _, existing := range c.recursiveGenericCache[def] {
		if typeSlicesEqual(existing.Arguments, args) {
			// Only backfill the body when this instance is not currently
			// being built: while building, the instance itself represents the
			// recursive occurrence and has to be returned as is to close the
			// type graph cycle.
			if existing.Body == nil && def.Type != nil && !c.recursiveGenericIsBuilding(def, existing) {
				existing.Body = c.buildRecursiveGenericBody(def, args)
			}
			return existing
		}
	}

	marker := types.NewRecursiveGeneric(def, args, nil)
	c.recursiveGenericCache[def] = append(c.recursiveGenericCache[def], marker)

	if def.Type != nil {
		c.recursiveGenericBuildingPush(def, marker)
		marker.Body = c.buildRecursiveGenericBody(def, args)
		c.recursiveGenericBuildingPop(def)
	}

	return marker
}

func (c *Checker) recursiveGenericIsBuilding(def *types.GenericNamedType, marker *types.RecursiveGeneric) bool {
	for _, building := range c.recursiveGenericBuilding[def] {
		if building == marker {
			return true
		}
	}
	return false
}

func (c *Checker) recursiveGenericBuildingPush(def *types.GenericNamedType, marker *types.RecursiveGeneric) {
	if c.recursiveGenericBuilding == nil {
		c.recursiveGenericBuilding = make(map[*types.GenericNamedType][]*types.RecursiveGeneric)
	}
	c.recursiveGenericBuilding[def] = append(c.recursiveGenericBuilding[def], marker)
}

func (c *Checker) recursiveGenericBuildingPop(def *types.GenericNamedType) {
	entries := c.recursiveGenericBuilding[def]
	c.recursiveGenericBuilding[def] = entries[:len(entries)-1]
}

// recursiveGenericFromArguments creates the transparent recursive instance
// for the given definition from checked type arguments, preserving their
// declaration order.
func (c *Checker) recursiveGenericFromArguments(def *types.GenericNamedType, typeArguments *types.TypeArguments) *types.RecursiveGeneric {
	args := make([]types.Type, 0, len(def.TypeParameters))
	for _, name := range typeArguments.ArgumentOrder {
		arg := typeArguments.ArgumentMap[name]
		if arg == nil {
			continue
		}
		args = append(args, arg.Type)
	}

	return c.internRecursiveGeneric(def, args)
}

func (c *Checker) buildRecursiveGenericBody(def *types.GenericNamedType, args []types.Type) types.Type {
	argMap := make(types.TypeArgumentMap, len(def.TypeParameters))
	for i, param := range def.TypeParameters {
		if i < len(args) {
			argMap[param.Name] = types.NewTypeArgument(args[i], types.INVARIANT)
		} else {
			argMap[param.Name] = types.NewTypeArgument(param.InferredType(), types.INVARIANT)
		}
	}

	return c._replaceTypeParameters(def.Type, argMap, false)
}

// recursiveGenericBody unfolds the transparent recursive instance to its
// body. When the definition is still being checked the marker itself is
// returned.
func (c *Checker) recursiveGenericBody(marker *types.RecursiveGeneric) types.Type {
	if marker.Body != nil {
		return marker.Body
	}
	if marker.Definition == nil || marker.Definition.Type == nil {
		return marker
	}

	return c.internRecursiveGeneric(marker.Definition, marker.Arguments).Body
}

// unfoldTransparentType strips transparent typedef wrappers (named aliases
// and recursive generic instances) until a non transparent constructor is
// reached. Cyclic alias chains terminate at the first repeated node and
// aliases whose body is still being checked are kept opaque.
func (c *Checker) unfoldTransparentType(t types.Type) types.Type {
	seen := make(map[types.Type]struct{})
	for {
		switch n := t.(type) {
		case *types.NamedType:
			if n.Type == nil {
				return t
			}
			if _, ok := seen[t]; ok {
				return t
			}
			seen[t] = struct{}{}
			t = n.Type
		case *types.RecursiveGeneric:
			body := c.recursiveGenericBody(n)
			if body == nil || body == t {
				return t
			}
			if _, ok := seen[t]; ok {
				return t
			}
			seen[t] = struct{}{}
			t = body
		default:
			return t
		}
	}
}

// Returns true when the pair is already being proven coinductively.
func (c *Checker) hasSubtypeAssumption(a, b types.Type) bool {
	for i := range c.activeSubtypePairs {
		pair := &c.activeSubtypePairs[i]
		if pair.a == a && pair.b == b {
			return true
		}
	}
	return false
}

func (c *Checker) pushSubtypeAssumption(a, b types.Type) {
	c.activeSubtypePairs = append(c.activeSubtypePairs, subtypePair{a: a, b: b})
}

func (c *Checker) popSubtypeAssumption() {
	c.activeSubtypePairs = c.activeSubtypePairs[:len(c.activeSubtypePairs)-1]
}

// Returns true when the pair is already being proven coinductively.
func (c *Checker) hasIntersectAssumption(a, b types.Type) bool {
	for i := range c.activeIntersectPairs {
		pair := &c.activeIntersectPairs[i]
		if pair.a == a && pair.b == b {
			return true
		}
	}
	return false
}

func (c *Checker) pushIntersectAssumption(a, b types.Type) {
	c.activeIntersectPairs = append(c.activeIntersectPairs, intersectPair{a: a, b: b})
}

func (c *Checker) popIntersectAssumption() {
	c.activeIntersectPairs = c.activeIntersectPairs[:len(c.activeIntersectPairs)-1]
}
