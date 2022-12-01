How to submit a pull request with minimal amounts of noise
==========================================================

This guide will show you how to:
- make sure you have no diff in dist/ or hints/, and therefore can safely merge
  origin/main
- add only the hints that you need to get a green
- add only the dist/ diff that is relevant for your PR.

Basics
------

Make sure you have the latest F\* and karamel, and the code works locally.

Discarding your local changes to dist/ and hints/
-------------------------------------------------

This first step allows merging upstream without conflicts.

```
git fetch
# You now have in your local git tree all the most recent refs for remote origin
git reset origin/main hints dist/*/*
# Both directories are now, in the staging area, the same as origin/main, but
# they have not changed in your working tree
git checkout hints dist/*/*
# The local modifications vis à vis the staging area have now been discarded:
# both your working tree and the staging area are the same as origin/main
```

At this stage, commit:

```
git commit -am "Reset hints and dist to be the same as main"
```

You can now merge main without fear of conflicts:

```
git merge origin/main
```

Fixing up the build
-------------------

Your working directory is now up-to-date with origin/main. To be 100% sure your
PR is going to get a green, restart from a clean build.

```
git clean -fdx dist hints
```

Now, run the build both locally and on CI. It's highly likely that some source
files will need fixes to verify again. If your new files do not pass CI at this
stage, rework your proofs to be more stable, e.g. fuel/ifuel 0, calc, etc. etc.

If some other files cause difficulties and you have no other choice (e.g.
discrepancy between platforms with no access to another platform), *selectively*
add hint files, and make sure to mention these problems in your pull request:

```
git add hints/Hacl.Poly1305.UnstableLemmas.fst.hints
git commit -m "Selected hints for failing files"
```

Push again and verify that you pass CI. Don't use `git commit -a`!

Adding the generated C code
---------------------------

By now all of your files should verify successfully. It is time to see if you
forgot to tweak some bundles. Use `git status` to see what's up. Iterate as
follows:

```
rm -rf dist/*/Makefile.basic && git clean -fdx dist && NODEPEND=1 make -j
```

This will force just the regeneration of the snapshots.

NOTE: if the problem is with Mozilla, you need to edit dist/package-mozilla.sh
and run `NODEPEND=1 make -j package-compile-mozilla` instead.

Once you have a successful local build, review the diff in `dist`:

```
git diff dist
```

If you see a million small-ish changes, maybe F\*/KaRaMeL are out of date.

At this stage, assess the situation, but in almost all cases, you can get away
with submitting JUST the diff for dist/gcc-compatible (unless you're
specifically working on MSVC-related stuff).

```
git add dist/gcc-compatible
git commit -m "Add changes to the C files as part of this PR"
```

Push and check that it passes CI.

Document the changes
--------------------

If your changes add a new algorithm or feature, or affect performance,
or change any public APIs, please add an entry to `CHANGES.md`.
You do not need to add an entry for proof fixes and improvements.

Opening the pull request
------------------------

To open a PR, you will need to follow the PR template in `pull_request_template.md`.

Once the PR is open, the HACL\* maintainers and other users will interact with you
on the PR and the PR will be merged once it has two approving reviews (including
one from the maintainers) and all CI checks pass.

All interactions are governed by the HACL\* code of conduct documented in `CODE_OF_CONDUCT.md`.
