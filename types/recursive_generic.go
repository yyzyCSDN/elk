package types

import (
	"strings"
)

// RecursiveGeneric is a checker-internal, fully transparent reference to an
// instantiated recursive generic typedef, eg. the occurrence of `A[T]` inside
// the body of:
//
//	typedef A[T] = T | ArrayList[A[T]]
//
// It behaves exactly as the body of its Definition with the definition's type
// parameters replaced by Arguments. It is erased completely after type
// checking and therefore never introduces any runtime wrapper object.
type RecursiveGeneric struct {
	Definition *GenericNamedType
	Arguments  []Type
	Body       Type // body of Definition with its parameters replaced by Arguments
}

func NewRecursiveGeneric(definition *GenericNamedType, arguments []Type, body Type) *RecursiveGeneric {
	return &RecursiveGeneric{
		Definition: definition,
		Arguments:  arguments,
		Body:       body,
	}
}

// traverse only visits the arguments, never the body, as the body contains
// this node (or another recursive node) and would loop forever.
func (r *RecursiveGeneric) traverse(parent Type, enter func(node, parent Type) TraverseOption, leave func(node, parent Type) TraverseOption) TraverseOption {
	switch enter(r, parent) {
	case TraverseBreak:
		return TraverseBreak
	case TraverseSkip:
		return leave(r, parent)
	}

	for _, argument := range r.Arguments {
		if argument.traverse(r, enter, leave) == TraverseBreak {
			return TraverseBreak
		}
	}

	return leave(r, parent)
}

func (r *RecursiveGeneric) ToNonLiteral(env *GlobalEnvironment) Type {
	return r
}

func (*RecursiveGeneric) IsLiteral() bool {
	return false
}

func (r *RecursiveGeneric) inspect() string {
	if len(r.Arguments) < 1 {
		return r.Definition.Name
	}

	buffer := new(strings.Builder)
	buffer.WriteString(r.Definition.Name)
	buffer.WriteRune('[')
	for i, argument := range r.Arguments {
		if i > 0 {
			buffer.WriteString(", ")
		}
		buffer.WriteString(Inspect(argument))
	}
	buffer.WriteRune(']')
	return buffer.String()
}

func (r *RecursiveGeneric) Copy() *RecursiveGeneric {
	return &RecursiveGeneric{
		Definition: r.Definition,
		Arguments:  r.Arguments,
		Body:       r.Body,
	}
}

// DeepCopyEnv remaps the definition to its copy in newEnv and deep copies the
// arguments. The body is rebuilt lazily by the checker from the copied
// definition, hence it is intentionally not copied here.
func (r *RecursiveGeneric) DeepCopyEnv(oldEnv, newEnv *GlobalEnvironment) *RecursiveGeneric {
	definition := r.Definition
	if copiedDefinition, ok := NameToTypeOk(r.Definition.Name, newEnv); ok {
		if newGenericNamed, ok := copiedDefinition.(*GenericNamedType); ok {
			definition = newGenericNamed
		}
	}

	var arguments []Type
	if len(r.Arguments) > 0 {
		arguments = make([]Type, len(r.Arguments))
		for i, argument := range r.Arguments {
			arguments[i] = DeepCopyEnv(argument, oldEnv, newEnv)
		}
	}

	return &RecursiveGeneric{
		Definition: definition,
		Arguments:  arguments,
	}
}
