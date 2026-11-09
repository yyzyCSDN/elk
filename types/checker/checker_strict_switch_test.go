package checker_test

import (
	"strings"
	"testing"

	"github.com/elk-language/elk/bitfield"
	"github.com/elk-language/elk/position/diagnostic"
	"github.com/elk-language/elk/types/checker"
	"github.com/elk-language/elk/vm"
)

// Some environments (notably the Windows checkout used while developing)
// cannot resolve the builtin import glob and therefore never produce the
// real checker diagnostics. The exhaustive behavior is fully exercised on
// the Linux CI, so skip the assertions instead of failing spuriously there.
var strictSwitchBuiltinsAvailable = func() bool {
	_, err := checker.CheckSource("<probe>", "1", nil, bitfield.BitField16{}, vm.DefaultThreadPool)
	for _, d := range err {
		if strings.HasPrefix(d.Message, "no matched files for import:") {
			return false
		}
	}
	return true
}()

func skipWhenBuiltinsUnavailable(t *testing.T) {
	t.Helper()
	if !strictSwitchBuiltinsAvailable {
		t.Skip("builtin imports cannot be resolved in this environment")
	}
}

type diagnosticSummary struct {
	severity diagnostic.Severity
	message  string
}

func strictSwitchDiagnostics(source string) []diagnosticSummary {
	_, err := checker.CheckSource("<main>", source, nil, bitfield.BitField16{}, vm.DefaultThreadPool)
	var result []diagnosticSummary
	for _, d := range err {
		// The Windows test environment cannot resolve the builtin glob,
		// filter that unrelated environmental diagnostic everywhere.
		if strings.HasPrefix(d.Message, "no matched files for import:") {
			continue
		}
		result = append(result, diagnosticSummary{
			severity: d.Severity,
			message:  d.Message,
		})
	}
	return result
}

func assertNoFailures(t *testing.T, name, source string) {
	t.Helper()
	for _, d := range strictSwitchDiagnostics(source) {
		if d.severity == diagnostic.FAIL {
			t.Errorf("%s: unexpected failure: %s", name, d.message)
		}
	}
}

func assertFailureContains(t *testing.T, name, source, fragment string) {
	t.Helper()
	var found bool
	for _, d := range strictSwitchDiagnostics(source) {
		if d.severity == diagnostic.FAIL && strings.Contains(d.message, fragment) {
			found = true
		}
	}
	if !found {
		t.Errorf("%s: expected a failure containing %q", name, fragment)
	}
}

func assertWarningContains(t *testing.T, name, source, fragment string) {
	t.Helper()
	var found bool
	for _, d := range strictSwitchDiagnostics(source) {
		if d.severity == diagnostic.WARN && strings.Contains(d.message, fragment) {
			found = true
		}
	}
	if !found {
		t.Errorf("%s: expected a warning containing %q", name, fragment)
	}
}

func TestStrictSwitchExhaustiveness(t *testing.T) {
	exhaustiveCases := map[string]string{
		"bool literals": `
			var a: Bool = true
			var b: Symbol = switch! a
			case true then :t
			case false then :f
			end
		`,
		"int literal union": `
			var a: 1 | 2 | 3 = 1
			switch! a
			case 1 then :a
			case 2 then :b
			case 3 then :c
			end
		`,
		"string and symbol union": `
			var a: "a" | :b | nil = nil
			switch! a
			case "a" then :string
			case :b then :symbol
			case nil then :nil
			end
		`,
		"nilable with binding": `
			var a: String? = nil
			switch! a
			case nil then :n
			case s then :s
			end
		`,
		"nilable pattern": `
			var a: String? = nil
			switch! a
			case s? then :s
			end
		`,
		"must and nil": `
			var a: Int? = 1
			switch! a
			case must then :v
			case nil then :n
			end
		`,
		"or and as patterns": `
			var a: 1 | 2 | nil = 1
			switch! a
			case nil then :n
			case (1 || 2) as x then :x
			end
		`,
		"and patterns": `
			var a: 1 | 2 | 3 = 1
			switch! a
			case x && 1 then :one
			case x && 2 then :two
			case x && 3 then :three
			end
		`,
		"list rest covers every length": `
			var a: ArrayList[Int] = []
			switch! a
			case [*] then :all
			end
		`,
		"list rest in the middle": `
			var a: ArrayList[Int] = []
			switch! a
			case [first, *middle, last] then :three
			case [*] then :any
			end
		`,
		"joint length and position coverage": `
			var a: ArrayList[1 | 2] = []
			switch! a
			case [] then :empty
			case [1] then :one
			case [2, *rest] then :rest
			end
		`,
		"tuple exhaustive": `
			var a: ArrayTuple[1 | 2] = %[]
			switch! a
			case %[] then :empty
			case %[1, *r] then :one
			case %[2, *r] then :two
			end
		`,
		"nested list patterns": `
			var a: ArrayList[ArrayList[Int]] = []
			switch! a
			case [[*], *rest] then :n
			case [] then :empty
			end
		`,
		"union of list and nil": `
			var a: ArrayList[Int]? = nil
			switch! a
			case nil then :n
			case [*] then :l
			end
		`,
		"or inside list pattern": `
			var a: ArrayList[1 | 2 | 3] = []
			switch! a
			case [] then :empty
			case [(1 || 2), *r] then :prefix
			case [3, *r] then :three
			end
		`,
		"binding covers any": `
			var a: any = 1
			var b: Symbol = switch! a
			case x then :x
			end
		`,
		"wildcard over plain int": `
			var a: Int = 1
			var b: Symbol = switch! a
			case 1 then :one
			case x then :any
			end
		`,
		"else branch is a fallback": `
			var a: String = "x"
			var b: Symbol = switch! a
			case %/x/ then :r
			else :e
			end
		`,
		"pure branches re-prove after dynamic branch": `
			var a: "x" | "y" = "x"
			switch! a
			case %/x/ then :r
			case "x" then :x
			case "y" then :y
			end
		`,
	}

	for name, source := range exhaustiveCases {
		t.Run(name, func(t *testing.T) {
			skipWhenBuiltinsUnavailable(t)
			assertNoFailures(t, name, source)
		})
	}
}

func TestStrictSwitchMissingValues(t *testing.T) {
	missingCases := map[string]string{
		"missing bool":          "no branch matches the value false",
		"missing int union":     "no branch matches the value 3",
		"missing string union":  `no branch matches the value "b"`,
		"missing symbol union":  "no branch matches the value :bar",
		"missing nil":           "no branch matches the value nil",
		"missing empty list":    "no branch matches the value []",
		"missing list position": "no branch matches the value [2]",
		"missing nested list":   "no branch matches the value [[]]",
		"missing empty tuple":   "no branch matches the value %[]",
		"missing negative int":  "no branch matches the value 0",
	}

	sources := map[string]string{
		"missing bool": `
			var a: Bool = true
			switch! a
			case true then :t
			end
		`,
		"missing int union": `
			var a: 1 | 2 | 3 = 1
			switch! a
			case 1 then :a
			case 2 then :b
			end
		`,
		"missing string union": `
			var a: "a" | "b" = "a"
			switch! a
			case "a" then :a
			end
		`,
		"missing symbol union": `
			var a: :foo | :bar = :foo
			switch! a
			case :foo then :f
			end
		`,
		"missing nil": `
			var a: Int? = 1
			switch! a
			case must then :v
			end
		`,
		"missing empty list": `
			var a: ArrayList[Int] = []
			switch! a
			case [x] then :one
			end
		`,
		"missing list position": `
			var a: ArrayList[1 | 2] = []
			switch! a
			case [] then :empty
			case [1, *r] then :one
			end
		`,
		"missing nested list": `
			var a: ArrayList[ArrayList[1 | 2]] = []
			switch! a
			case [] then :empty
			case [[1], *r] then :one
			case [[2], *r] then :two
			end
		`,
		"missing empty tuple": `
			var a: ArrayTuple[1 | 2] = %[]
			switch! a
			case %[1, *r] then :one
			case %[2, *r] then :two
			end
		`,
		"missing negative int": `
			var a: -1 | 0 | 1 = 0
			switch! a
			case -1 then :neg
			case 1 then :pos
			end
		`,
	}

	for name, fragment := range missingCases {
		t.Run(name, func(t *testing.T) {
			skipWhenBuiltinsUnavailable(t)
			assertFailureContains(t, name, sources[name], fragment)
		})
	}
}

func TestStrictSwitchDynamicPatterns(t *testing.T) {
	const cannotProve = "cannot prove exhaustiveness"

	dynamicCases := map[string]string{
		"regex pattern": `
			var a: String = "x"
			switch! a
			case %/x/ then :r
			case "y" then :y
			end
		`,
		"object getter pattern": `
			var a: String = "x"
			switch! a
			case String(length: 1) then :one
			case "y" then :y
			end
		`,
		"dynamic equality pattern": `
			var a: 1 | 2 | 3 = 1
			switch! a
			case == 1 then :one
			case 2 then :two
			case 3 then :three
			end
		`,
		"relational pattern": `
			var a: 1 | 2 | 3 = 1
			switch! a
			case < 3 then :small
			case 3 then :three
			end
		`,
	}

	for name, source := range dynamicCases {
		t.Run(name, func(t *testing.T) {
			skipWhenBuiltinsUnavailable(t)
			assertFailureContains(t, name, source, cannotProve)
		})
	}

	t.Run("no fabricated witness when proof is impossible", func(t *testing.T) {
		skipWhenBuiltinsUnavailable(t)
		for _, d := range strictSwitchDiagnostics(dynamicCases["regex pattern"]) {
			if d.severity == diagnostic.FAIL && strings.Contains(d.message, "no branch matches") {
				t.Fatalf("did not expect a concrete witness for dynamic patterns: %s", d.message)
			}
		}
	})
}

func TestStrictSwitchUnreachableBranches(t *testing.T) {
	skipWhenBuiltinsUnavailable(t)
	source := `
		var a: Bool = true
		switch! a
		case true then :t
		case false then :f
		case true then :x
		end
	`
	assertWarningContains(t, "unreachable pure branch", source, "this branch is unreachable")

	// The warning must not be accompanied by an exhaustiveness failure.
	for _, d := range strictSwitchDiagnostics(source) {
		if d.severity == diagnostic.FAIL && strings.Contains(d.message, "non-exhaustive") {
			t.Fatalf("expected the switch to remain exhaustive: %s", d.message)
		}
	}
}

func TestStrictSwitchResultTypeHasNoNil(t *testing.T) {
	skipWhenBuiltinsUnavailable(t)
	// An exhaustive switch! must not inject nil into its result type, so
	// assigning the result to a non nilable symbol type has to succeed.
	exhaustive := `
		var a: 1 | 2 = 1
		var b: Symbol = switch! a
		case 1 then :one
		case 2 then :two
		end
	`
	assertNoFailures(t, "exhaustive result without nil", exhaustive)

	// The same non exhaustive switch without else keeps the regular
	// behaviour and adds nil to the result type.
	regular := `
		var a: 1 | 2 = 1
		var b: Symbol = switch a
		case 1 then :one
		end
	`
	assertFailureContains(t, "regular switch keeps nil result", regular, "cannot be assigned to type `Std::Symbol`")
}
