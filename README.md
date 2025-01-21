# topos

A lean 4 port of content from the lean 3 topos library at [b-mehta/topos](https://github.com/b-mehta/topos). The content of this repository follows Mac Lane and Moerdijk's "Sheaves in Geometry and Logic" and is currently incomplete. The eventual goal is to contribute this code to [mathlib4](https://github.com/leanprover-community/mathlib4).

## TODO

- Finish `Topos/Colimits.lean` thereby verifying that a topos has all finite colimits.
- Create `Topos/Example.lean` and formally verify that existing instances of topoi (sets, sheaves on sites) are topoi.
- Chores relating to making this repository [mathlib friendly](https://leanprover-community.github.io/contribute/index.html).
