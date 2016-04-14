Notes for an eventual parsers paper
===================================

## Things done in Coq to speed up synthesis
- Preoptimize the parser, before we know the grammar
  . By refinement, with tactics (good? bad? not sure?)
  . Tag things as fully reducible on the nth iteration of reduction, tactic that propogates information
- Use explicit reduction lists, not `simpl`
- `vm_compute in` is broken
- `abstract` in TC resolution to not retypecheck things so much
- split up refinement to not rewrite over the whole term
  . iterated `impl` rather than iterated `and`
- split reduction into fully-reducible (compute/vm_compute) by reflection,

## Things done for OCaml speed
- Fewer allocations
  . flatten product types for well-founded Fix data
  . n-ary Fix equality lemmas
- make things tail-recursive
- eliminate string comparison tests
- OCaml strings
- only pass around indexes for substrings
