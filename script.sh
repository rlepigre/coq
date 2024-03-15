#!/bin/bash
set -euo pipefail

BASE="v8.19"
TAG="V8.19.1+bedrock"
REMOTE="rlepigre"
PUSH="true"
FETCH="true"

if [[ "$FETCH" == "true" ]]; then
  git fetch --all
else
  echo "Not fetching any remotes."
fi

REMOTE_URL="$(git remote get-url $REMOTE)"
REMOTE_PATH="${REMOTE_URL#"git@github.com:"}"
REMOTE_PATH="${REMOTE_PATH%".git"}"
if [[ "$REMOTE_URL" != "git@github.com:$REMOTE_PATH.git" ]]; then
  echo "The extracted remote path ($REMOTE_PATH) does not look right."
  exit 1
fi

# Reset to the version tag, to allow re-running the script.
mv script.sh script.sh.backup
git reset --hard "$BASE"
mv script.sh.backup script.sh

# Picking a merge commit from master.
pick () {
  git cherry-pick -m 1 ${1}
}

# PR #18327: unification fix (primitive projections change).
pick 592760a932ab7f606e0151bb6d3bf994f5d944c7

# PR #18432: Ltac2 typed notations.
pick 0c1a6d092b3d260e7fb745402d53b8c87ad4eecf

# PR #18641: warn on unused Ltac2 variables
# FIXME needs to be merged upstream (draft).
pick 4bc790985e1408a7bac06cd1a72bda2609b2f82b

# PR #18675: fix unfold tactic not unfolding compatibility constants
pick 0aad99ebdc75fc5d00a406bb9bd901dcc6bba5e0

# PR 18688: use more tail-recursion in lia to avoid stack overflows.
pick 009deb7fdd9f33d7cd56bffe9719f54f3834b3d3

# PR 14291: Add the primitive catch_system to the logic monad.
pick b95b0eca6908c5bcd61a6727d7677d7046a881be

# PR 18769: Recompute stored projection constant.
pick a256e825245fa7f09f4d17f8b48b03df89cfd80b

# PR 18762: Strictly unique classes can be resolved independently.
# FIXME needs to be merged upstream
pick 0f9b9d66975166ecfedaac69d6b1afa7fa788e36

# PR 18785: Restore ability to make primitive projections hint opaque.
# FIXME: this is from a specific branch, we cannot cherry-pick the original.
pick ddb7cf51864beda27c97ade51b95b0ce69566aa5
pick 38cc442d35f4b001b210143a57dafe2b0e9f3410
pick e472b130cbaaf5d91aaa842423343ad75bfecbfa

# PR 18809: Fix Strategy/with_strategy: set projection opacity.
# FIXME needs to be merged upstream.
pick 96bb15c82c23316daa30ff47ddf10c063bc2f96b

# PR 18791: Make projection comparison functions antisymmetric.
# FIXME needs to be merged upstream (approved already).
pick 2a979e5b2eb8f5858399f474084dc131b97708a7


# Recording the script.
git add script.sh
git commit \
  -m "Cherry-picking script used to create this branch." \
  --author "Rodolphe Lepigre <rodolphe@bedrocksystems.com>"

# Tagging and pushing.
if [[ "$PUSH" != "true" ]]; then
  echo "Skipping the tagging."
  exit 0;
fi

git tag -f "$TAG"
git push --force-with-lease --set-upstream "$REMOTE"
git push -f --tags

echo "Sleeping for 10 seconds..."
sleep 10

wget "https://github.com/$REMOTE_PATH/archive/refs/tags/$TAG.tar.gz"

echo "md5=$(md5sum "$TAG.tar.gz" | cut -d' ' -f1)"
echo "sha512=$(sha512sum "$TAG.tar.gz" | cut -d' ' -f1)"
rm "$TAG.tar.gz"
