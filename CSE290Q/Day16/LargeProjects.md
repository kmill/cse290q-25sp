# Some examples of large formalization projects

## Freek Wiedijk's 100 theorems list

https://www.cs.ru.nl/~freek/100/

## Lean's Mathlib
https://github.com/leanprover-community/mathlib4

Generally contributions come from ongoing formalization projects.
Goal: be an *integrated* and *coherent* library of
modern theoretical mathematics.
It is up to a PR author to update Mathlib if it is a breaking change,
but downstream projects are responsible for updating themselves.
Rolling releases, with tagged versions on each Lean release.

https://leanprover-community.github.io/mathlib_stats.html
105718 Definitions
215059 Theorems
576 Contributors	

## Isabelle's Archive of Formal Proofs

https://www.isa-afp.org/

https://www.isa-afp.org/statistics/
903 Entries
537 Authors
~290,300 Lemmas
~4,755,800 Lines of Code

Contributions are relatively independent.
Contributions can be updated, and it's the responsibility of
the author to update all contributions that depend on it.

## Mizar's Journal of Formalized Mathematics

https://mizar.uwb.edu.pl/JFM/
(Last I checked, about 3mm lines)

Contributions are mostly independent from one another,
but papers can depend on previous papers.

## Projects using Lean Blueprints

https://github.com/PatrickMassot/leanblueprint

Patrick Massot developed a technique for successfully carrying out
large-scale formalization projects. Elements:

- Create a detailed "blueprint" document.
  It is the mathematics written in a much more rigorous style,
  with theorems/lemmas with much finer granularity.
  (Many more "technical" lemmas than you normally see!)

- Create a parallel "formal blueprint" that has Lean formalizations
  of corresponding statements in the blueprint.

- Do this all in a way that links blueprints together.
  Massot's tool does this using LaTeX macros.

- Also, publish the blueprints as a webpage, keep all code in a
  GitHub repository, and advertise the ongoing project.
  Recruit people to help.

On top of this, you can use a Polymath-project-style project management
technique, where as the leader of the project you create posts of
ongoing work, what needs to be done, and invite people to claim tasks
in the formal blueprint.

Note: often this is not done using a "waterfall" development.
Writing a blueprint document requires iteration. Difficulties creating
the formal blueprint inform how to write the original blueprint.

Example: In the [Carleson project](https://florisvandoorn.com/carleson/),
the project's blueprint has eventually become a 160 page document, after
a number of false starts. (If I remember correctly, it started at about
30 pages.)

## Cedar at Amazon Web Services (AWS)

I don't have much insight about the development process itself here.
Originally, Cedar was formally verified using Dafny, and later they
created a verified Lean implementation.

https://aws.amazon.com/blogs/opensource/lean-into-verified-software-development/
https://arxiv.org/pdf/2403.04651

## AI training data

Too many to link to. AI companies are putting money into trying to
solve autoformalization's data scarcity problem by compiling large
databases of "high-quality" examples of informal statements and proofs.

# Tools for finding things

Searching
https://leanprover-community.github.io/mathlib4_docs/index.html
Every theorem uses the mathlib naming scheme, which is often predictable.

Lean Zulip: **Is there code for X?**
This is a great place to ask if something exists in Mathlib,
or if what stepping stones are already there,
or if there is a project that already exists with it formalized.

Other search tools:
* https://leansearch.net/ (using LLMs)
* https://loogle.lean-lang.org/ (using plain old unification)

In the end, just like the mathematical literature,
you often find things by knowing someone who knows where something is.

Gap: formalized textbooks.