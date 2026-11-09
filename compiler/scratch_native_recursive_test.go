package compiler_test

import (
	"bytes"
	"go/format"
	"testing"

	"github.com/elk-language/elk/bitfield"
	"github.com/elk-language/elk/compiler/types"
	"github.com/elk-language/elk/types/checker"
	"github.com/elk-language/elk/vm"
)

func TestScratchNativeRecursive(t *testing.T) {
	input := `
		typedef Json = nil | Int | String | ArrayList[Json] | HashRecord[String, Json]

		var xs: ArrayList[Json] = [1, "two"]
		var a: Json = xs
		var b: Json = 1
		var n: Int = xs.length
	`

	var buff bytes.Buffer
	comp, errs := checker.CheckSourceNative(
		"<main>",
		input,
		nil,
		bitfield.BitField16FromBitFlag(checker.BuiltinImportsProcessedFlag),
		&buff,
		vm.DefaultThreadPool,
	)
	if errs.IsFailure() {
		t.Fatalf("errors: %v", errs)
	}
	comp.Flush()
	result, err := format.Source(buff.Bytes())
	if err != nil {
		t.Log(buff.String())
		t.Fatalf("cannot format go source: %s", err)
	}

	goChecker := types.NewGoTypecheckerWithImporter(goImporter)
	if err := goChecker.CheckBytes(result); err != nil {
		t.Log(string(result))
		t.Fatalf("generated go does not typecheck: %s", err)
	}
}
