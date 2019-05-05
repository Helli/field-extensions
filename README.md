# field-extensions
Field Extensions in HOL-Algebra – an interdisciplinary verification project based on Isabelle2019-RC1.

The theories in _VectorSpace_by_HoldenLee/_ stem from the *Archive of Formal Proofs* (AFP), cf. https://devel.isa-afp.org/entries/VectorSpace.html and
https://devel.isa-afp.org/browser_info/current/AFP/Jordan_Normal_Form/Missing_VectorSpace.html.
I have slightly adjusted them to better use the new HOL-Algebra:

- In RingModuleFacts.thy, I removed the now-superseded facts *lmult_0* and *rmult_0*, and the constant *units_group*, which duplicates *Group.units_of*.
- In MonoidSums, *finprod_all1* is superseded by *finprod_one_eqI*. The lemmas *factors_equal*/*summands_equal* are trivial and
unused in the AFP.
- In LinearCombinations, I replaced the definition *submodule* by *Module.submodule*. Careful: The latter does not
assume the superstructure to be a module. This may affect statements in descendant theories. Moreover, I needed to adjust the argument order. (The converse change, namely adjusting *Module.submodule*'s argument order, might have been the easier way in retrospect.) Furthermore, I removed some confusing junk from within the definition of *func_space*.
- In SumSpaces, I once again clarified a definition. I also slightly relaxed the type constraint on *inj1* and *inj2*, one
could further relax it to *ring_scheme*.
- In VectorSpace, I removed two superseded lemmas and changed the premise of *func_space_is_vs* to make it consistent with
*ring.func_space_is_module*.
- In Missing_VectorSpace, I removed *vectorspace.lincomb_distrib* which is just the symmetric of
*LinearCombinations.module.lincomb_smult*.

Documentation is available in _Doc/_. The session _Doc_ depends on the session in the main directory.
