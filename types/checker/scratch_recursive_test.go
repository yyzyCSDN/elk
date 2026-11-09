package checker_test

import (
	"testing"

	"github.com/elk-language/elk/bitfield"
	"github.com/elk-language/elk/position/diagnostic"
	"github.com/elk-language/elk/types/checker"
	"github.com/elk-language/elk/vm"
)

func runScratch(input string) diagnostic.DiagnosticList {
	_, errs := checker.CheckSource("<main>", input, nil, bitfield.BitField16{}, vm.DefaultThreadPool)
	return errs
}

func TestScratchRecursive(t *testing.T) {
	tests := testTable{
		"json model": {
			input: `
				typedef Json = nil | bool | Int | Float | String | ArrayList[Json] | HashRecord[String, Json]
				var n: Json = nil
				var f: Json = 1.2
				var onlyNil: ArrayList[Json] = [nil]
				var onlyFloat: ArrayList[Json] = [1.2]
				var intNil: ArrayList[Json] = [1, nil]
				var simple: ArrayList[Json] = [1, 2, 3]
				var inner: ArrayList[Json] = [1, 2.5, nil]
				var rec: HashRecord[String, Json] = %{"x" => inner}
				var a: ArrayList[Json] = ["x", 1, nil, rec]
				var j: Json = a
				var k: Json = rec
				var leaf: Json = "s"
			`,
		},
		"same shape different names compatible": {
			input: `
				typedef A = Int | ArrayList[A]
				typedef B = Int | ArrayList[B]
				var b: ArrayList[B] = [1]
				var x: A = b
			`,
		},
		"same shape different leaves incompatible": {
			input: `
				typedef A = Int | ArrayList[A]
				typedef B = String | ArrayList[B]
				var b: ArrayList[B] = ["x"]
				var x: A = b
			`,
			err: diagnostic.DiagnosticList{
				diagnostic.NewFailure(L("<main>", P(0, 0, 0), P(0, 0, 0)), "placeholder"),
			},
		},
		"json incompatible leaf": {
			input: `
				typedef Json = Int | String | ArrayList[Json]
				var a: Json = 1.2
			`,
			err: diagnostic.DiagnosticList{
				diagnostic.NewFailure(L("<main>", P(0, 0, 0), P(0, 0, 0)), "placeholder"),
			},
		},
		"generic tree": {
			input: `
				typedef Tree[T] = T | ArrayList[Tree[T]]
				var xs: ArrayList[Tree[Int]] = [1]
				var a: Tree[Int] = xs
				var leaf: Tree[Int] = 1
			`,
		},
		"generic tree bad leaf": {
			input: `
				typedef Tree[T] = T | ArrayList[Tree[T]]
				var a: Tree[Int] = "x"
			`,
			err: diagnostic.DiagnosticList{
				diagnostic.NewFailure(L("<main>", P(0, 0, 0), P(0, 0, 0)), "placeholder"),
			},
		},
		"mutual generic guarded": {
			input: `
				typedef A[T] = T | B[T]
				typedef B[U] = U | ArrayList[A[U]]
				var xs: ArrayList[A[Int]] = [1]
				var a: A[Int] = xs
				var viaB: B[Int] = 1
			`,
		},
		"unguarded self": {
			input: `
				typedef A = A
			`,
			err: diagnostic.DiagnosticList{
				diagnostic.NewFailure(L("<main>", P(0, 0, 0), P(0, 0, 0)), "placeholder"),
			},
		},
		"unguarded mutual": {
			input: `
				typedef Foo = Bar
				typedef Bar = Foo
			`,
			err: diagnostic.DiagnosticList{
				diagnostic.NewFailure(L("<main>", P(0, 0, 0), P(0, 0, 0)), "placeholder"),
			},
		},
		"wrapped args rejected": {
			input: `
				typedef A[T] = T | B[ArrayList[T]]
				typedef B[U] = U | ArrayList[A[U]]
			`,
			err: diagnostic.DiagnosticList{
				diagnostic.NewFailure(L("<main>", P(0, 0, 0), P(0, 0, 0)), "placeholder"),
			},
		},
		"changed args rejected": {
			input: `
				typedef A[T] = T | B[Int]
				typedef B[U] = U | ArrayList[A[U]]
			`,
			err: diagnostic.DiagnosticList{
				diagnostic.NewFailure(L("<main>", P(0, 0, 0), P(0, 0, 0)), "placeholder"),
			},
		},
		"other constructor rejected": {
			input: `
				typedef A = Box[A]
			`,
			err: diagnostic.DiagnosticList{
				diagnostic.NewFailure(L("<main>", P(0, 0, 0), P(0, 0, 0)), "placeholder"),
			},
		},
		"nilable only rejected": {
			input: `
				typedef A = A?
			`,
			err: diagnostic.DiagnosticList{
				diagnostic.NewFailure(L("<main>", P(0, 0, 0), P(0, 0, 0)), "placeholder"),
			},
		},
		"nilable guarded accepted": {
			input: `
				typedef A = ArrayList[A]?
				var a: A = nil
			`,
		},
		"arity mismatch rejected": {
			input: `
				typedef A[T] = T | B
				typedef B = ArrayList[A[Int]]
			`,
			err: diagnostic.DiagnosticList{
				diagnostic.NewFailure(L("<main>", P(0, 0, 0), P(0, 0, 0)), "placeholder"),
			},
		},
		"singleton helper expansion": {
			input: `
				typedef Wrap[X] = ArrayList[X]
				typedef A[T] = T | Wrap[A[T]]
				var xs: ArrayList[A[Int]] = [1]
				var a: A[Int] = xs
			`,
		},
		"non generic helper expansion": {
			input: `
				typedef H = ArrayList[A]
				typedef A = H
				var xs: ArrayList[A] = []
				var a: A = xs
			`,
		},
		"leaf helper alias": {
			input: `
				typedef Leaves = Int | String
				typedef A = Leaves | ArrayList[A]
				var xs: ArrayList[A] = [1, "x"]
				var a: A = xs
			`,
		},
		"hashmap guard": {
			input: `
				typedef M = HashMap[String, M]
				var m: HashMap[String, M] = {}
				var x: M = m
			`,
		},
		"array tuple guard": {
			input: `
				typedef T2 = ArrayTuple[T2]
				var t: ArrayTuple[T2] = %[]
				var x: T2 = t
			`,
		},
		"method signatures": {
			input: `
				typedef Json = Int | String | ArrayList[Json]
				def parse(x: Json): Json
					return x
				end
				var a: Json = parse(1)
			`,
		},
		"generic bounds": {
			input: `
				typedef Json = Int | String | ArrayList[Json]
				def id[T < Json](x: T): T
					return x
				end
				var a: Json = id(1)
			`,
		},
		"bounds violation": {
			input: `
				typedef Json = Int | String | ArrayList[Json]
				def id[T <: Json](x: T): T
					return x
				end
				var a = id(1.2)
			`,
			err: diagnostic.DiagnosticList{
				diagnostic.NewFailure(L("<main>", P(0, 0, 0), P(0, 0, 0)), "placeholder"),
			},
		},
		"invariant containers": {
			input: `
				typedef Tree[T] = T | ArrayList[Tree[T]]
				var a: ArrayList[Tree[Int]] = []
				var b: ArrayList[Tree[Int64]] = a
			`,
			err: diagnostic.DiagnosticList{
				diagnostic.NewFailure(L("<main>", P(0, 0, 0), P(0, 0, 0)), "placeholder"),
			},
		},
		"method calls": {
			input: `
				typedef Json = Int | String | ArrayList[Json]
				var xs: ArrayList[Json] = [1, "x"]
				var n: Int = xs.length
			`,
		},
		"helper with wrapping arg rejected": {
			input: `
				typedef Wrap[X] = X
				typedef A[T] = T | Wrap[ArrayList[A[T]]]
			`,
			err: diagnostic.DiagnosticList{
				diagnostic.NewFailure(L("<main>", P(0, 0, 0), P(0, 0, 0)), "placeholder"),
			},
		},
		"union through helper guarded": {
			input: `
				typedef G[X] = ArrayList[X] | nil
				typedef A[T] = T | G[A[T]]
				var xs: ArrayList[A[Int]] = [1]
				var a: A[Int] = xs
				var z: A[Int] = nil
			`,
		},
	}

	for name, tc := range tests {
		t.Run(name, func(t *testing.T) {
			if len(tc.err) == 1 && tc.err[0].Message == "placeholder" {
				got := runScratch(tc.input)
				t.Logf("ERRORS for %s:", name)
				for _, e := range got {
					t.Logf("  %s: %s", e.Location, e.Message)
				}
				return
			}
			checkerTest(tc, t)
		})
	}
}
