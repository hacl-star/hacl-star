How to submit a pull request with minimal amounts of noise
==========================================================

Make sure you have the latest F\* and karamel.

Discarding your local changes to dist/ and hints/
-------------------------------------------------

```
git fetch
# You now have in your local git tree all the most recent refs for remote origin
git reset origin/master hints dist
# Both directories are now, in the staging area, the same as origin/master, but
# they have not changed in your working tree
git checkout hints dist
# The local modifications vis à vis the staging area have now been discarded:
# both your working tree and the staging area are the same as origin/master
```

Note: if you had changes to files in dist *OTHER* than the generated C files,
e.g. Makefile.tmpl, do the opposite operation, for instance:

```
git reset HEAD dist/Makefile.tmpl
git checkout dist/Makefile.tmpl
```

At this stage, commit:

```
git commit -am "Reset hints and dist to be the same as master"
```

You can now merge master without fear of conflicts:

```
git merge origin/master
```

Fixing up the build
-------------------

At this stage, discard ancient files and new hints:

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

Adding the snapshot
-------------------

At this stage you should see whether you forgot to tweak some bundles, e.g.
Mozilla only wants a subset of our algorithms and maybe you want to disable
yours for the time being so that it doesn't appear in the dist/mozilla
directory. Use `git status` to see what's up. Iterate as follows:

```
rm -rf dist/*/Makefile.basic && git clean -fdx dist && NODEPEND=1 make -j
```

This will force just the regeneration of the snapshots.

Once you have a successful local build, review the diff in `dist`:

```
git diff dist
```

if you see anything other than small changes, you most likely need to update F\*
and karamel. Start everything over again. Do not submit a pull request if
there's too much noise in those files.

If you are happy with the small amount of diff:

```
git add dist
git commit -m "New snapshot"
```

Push and check that it passes CI. Open pull request.
