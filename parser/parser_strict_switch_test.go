package parser

import (
	"testing"

	"github.com/elk-language/elk/parser/ast"
)

func collectSwitchNodes(node ast.Node) []*ast.SwitchExpressionNode {
	var result []*ast.SwitchExpressionNode
	ast.Traverse(node, func(node, _ ast.Node) ast.TraverseOption {
		if switchNode, ok := node.(*ast.SwitchExpressionNode); ok {
			result = append(result, switchNode)
		}
		return ast.TraverseContinue
	}, nil)
	return result
}

func TestStrictSwitchParsing(t *testing.T) {
	t.Run("marks adjacent switch! as exhaustive", func(t *testing.T) {
		program, err := Parse("<main>", `
switch! foo
case 1 then :one
case 2 then :two
else :other
end
`)
		if err.IsFailure() {
			t.Fatalf("unexpected parse errors: %s", err.Error())
		}

		switches := collectSwitchNodes(program)
		if len(switches) != 1 {
			t.Fatalf("expected one switch node, got %d", len(switches))
		}
		if !switches[0].Exhaustive {
			t.Fatal("expected the switch! node to be marked exhaustive")
		}
		if switches[0].String()[:7] != "switch!" {
			t.Fatalf("expected string representation to start with switch!, got %q", switches[0].String())
		}
	})

	t.Run("keeps regular switch non exhaustive", func(t *testing.T) {
		program, err := Parse("<main>", `
switch foo
case 1 then :one
end
`)
		if err.IsFailure() {
			t.Fatalf("unexpected parse errors: %s", err.Error())
		}

		switches := collectSwitchNodes(program)
		if len(switches) != 1 {
			t.Fatalf("expected one switch node, got %d", len(switches))
		}
		if switches[0].Exhaustive {
			t.Fatal("expected the regular switch node not to be exhaustive")
		}
	})

	t.Run("whitespace separates switch from logical not", func(t *testing.T) {
		// `switch !foo` must keep parsing `!foo` as the matched value and
		// must not turn the expression into an exhaustive switch.
		program, err := Parse("<main>", `
var foo: Bool = true
switch !foo
case true then :yes
else :no
end
`)
		if err.IsFailure() {
			t.Fatalf("unexpected parse errors: %s", err.Error())
		}

		switches := collectSwitchNodes(program)
		if len(switches) != 1 {
			t.Fatalf("expected one switch node, got %d", len(switches))
		}
		if switches[0].Exhaustive {
			t.Fatal("expected `switch !foo` not to be parsed as switch!")
		}
		if _, ok := switches[0].Value.(*ast.UnaryExpressionNode); !ok {
			t.Fatalf("expected the matched value to be a unary expression, got %T", switches[0].Value)
		}
	})
}
