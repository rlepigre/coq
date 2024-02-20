#!/bin/bash

# Reset to the version tag, to allow re-running the script.
mv script.sh script.sh.backup
git reset --hard v8.19
mv script.sh.backup script.sh

# Picking a merge commit from master.
pick () {
  git cherry-pick -m 1 ${1}
}

# PR #18327: unification fix (primitive projections change).
pick 592760a932ab7f606e0151bb6d3bf994f5d944c7

# PR #18641: warn on unused Ltac2 variables
# FIXME needs to be merged upstrea (draft).
pick 5176cf310a69705ab94b75c178df9a42aa32750d

# PR #18673: extension of the [FMap] Ltac2 module
# FIXME needs to be merged upstream.
pick c42a624e5fd4770a1379f6e84058e08e691e00cc
pick 72562942c22917c6b93d1eb35473d4b366b9528e

# PR #18675: fix unfold tactic not unfolding compatibility constants
pick a9bcb0ec8b19dc11bee4646a850192b5f5e8b4c6


# Recording the script.
git add script.sh
git commit \
  -m "Cherry-picking script used to create this branch." \
  --author "Rodolphe Lepigre <rodolphe@bedrocksystems.com>"

# Tagging and pushing.
TAG="V8.19.0+bedrock"
git tag -f "$TAG"
git push --force-with-lease
git push -f --tags

wget "https://github.com/rlepigre/coq/archive/refs/tags/$TAG.tar.gz"

echo "md5=$(md5sum "$TAG.tar.gz" | cut -d' ' -f1)"
echo "sha512=$(sha512sum "$TAG.tar.gz" | cut -d' ' -f1)"
rm "$TAG.tar.gz"
