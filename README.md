# field-extensions
field extensions in Isabelle/HOL (interdisciplinary project), based on isabelle-dev.
The theories in VectorSpace_by_HoldenLee stem from https://devel.isa-afp.org/entries/VectorSpace.html and
https://devel.isa-afp.org/browser_info/current/AFP/Jordan_Normal_Form/Missing_VectorSpace.html. I have slightly
adjusted VectorSpace to better use the new HOL-Algebra:

- In RingModuleFacts.thy, I removed the now-superseded facts lmult_0 and rmult_0,
   and the constant units_group, which duplicates Group.units_of
- In MonoidSums, finprod_all1 is superseded by finprod_one_eqI
- In LinearCombinations, I replaced the definition "submodule" by "Module.submodule". Careful: The latter does not
assume the superstructure to be a module. This may affect statements in descendant theories. Furthermore, I removed some
confusing junk from within the definition of direct_sum