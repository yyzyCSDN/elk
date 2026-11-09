package vm_test

import (
	"strings"
	"testing"

	"github.com/elk-language/elk/types/checker"
	"github.com/elk-language/elk/value"
	"github.com/elk-language/elk/vm"
)

func TestScratchRecursiveVM(t *testing.T) {
	vm.InitGlobalEnvironment()
	c := checker.New()
	c.SetREPL(true)

	// First input: define a recursive Json typedef and a recursive function
	// summing integer leaves inside lists.
	input1 := `
		typedef Json = Int | String | ArrayList[Json]
		def sum(x: Json): Int
			match x
				when is Int then return x
				when is String then return 0
				when is ArrayList[Json]
					var total := 0
					for el in x
						total = total + sum(el)
					end
					return total
			end
			return 0
		end
	`
	if _, errs := c.CheckSourceREPLBytecode("sourceName", input1, nil); errs.IsFailure() {
		t.Fatalf("input1 compile error: %s", errs.Error())
	}

	// Second input: use the previously defined recursive alias and function.
	input2 := `
		var xs: ArrayList[Json] = [1, 2, "ignored", [3, 4]]
		sum(xs)
	`
	chunk, errs := c.CheckSourceREPLBytecode("sourceName", input2, nil)
	if errs.IsFailure() {
		t.Fatalf("input2 compile error: %s", errs.Error())
	}

	var stdout strings.Builder
	v := vm.New(vm.WithStdout(&stdout))
	got, runtimeErr := v.InterpretTopLevel(chunk)
	if !runtimeErr.IsUndefined() {
		t.Fatalf("runtime error: %s", runtimeErr.Inspect())
	}
	if got.Inspect() != "10" {
		t.Fatalf("got %s, want 10", got.Inspect())
	}
}

func TestScratchRecursiveREPLRecovery(t *testing.T) {
	elk.InitGlobalEnvironment()
	c := checker.New()
	c.SetREPL(true)

	input1 := `
		typedef A = Int | ArrayList[A]
		var xs: ArrayList[A] = [1, 2]
	`
	if _, errs := c.CheckSourceREPLBytecode("sourceName", input1, nil); errs.IsFailure() {
		t.Fatalf("input1 compile error: %s", errs.Error())
	}

	// A failing input must not destroy the previously defined alias.
	bad := `
		var bad: A = "nope"
	`
	if _, errs := c.CheckSourceREPLBytecode("sourceName", bad, nil); !errs.IsFailure() {
		t.Fatal("expected failure for bad input")
	}

	// The recursive alias is still usable after the failed input.
	good := `
		var ok: ArrayList[A] = [3]
		ok.length
	`
	chunk, errs := c.CheckSourceREPLBytecode("sourceName", good, nil)
	if errs.IsFailure() {
		t.Fatalf("good input compile error: %s", errs.Error())
	}

	v := vm.New()
	got, runtimeErr := v.InterpretTopLevel(chunk)
	if !runtimeErr.IsUndefined() {
		t.Fatalf("runtime error: %s", runtimeErr.Inspect())
	}
	if got.Inspect() != "1" {
		t.Fatalf("got %s, want 1", got.Inspect())
	}
}

func TestScratchRecursiveREPLUnguardedRejected(t *testing.T) {
	elk.InitGlobalEnvironment()
	c := checker.New()
	c.SetREPL(true)

	// Unguarded recursion is rejected and the environment keeps working.
	bad := `
		typedef Bad = Bad
		var x := 1
	`
	if _, errs := c.CheckSourceREPLBytecode("sourceName", bad, nil); !errs.IsFailure() {
		t.Fatal("expected failure for unguarded recursion")
	}

	good := `
		typedef Ok = Int | ArrayList[Ok]
		var xs: ArrayList[Ok] = [1]
		xs.length
	`
	chunk, errs := c.CheckSourceREPLBytecode("sourceName", good, nil)
	if errs.IsFailure() {
		t.Fatalf("good input compile error: %s", errs.Error())
	}
	v := vm.New()
	got, runtimeErr := v.InterpretTopLevel(chunk)
	if !runtimeErr.IsUndefined() {
		t.Fatalf("runtime error: %s", runtimeErr.Inspect())
	}
	if got.Inspect() != "1" {
		t.Fatalf("got %s, want 1", got.Inspect())
	}
}

var _ value.Value
