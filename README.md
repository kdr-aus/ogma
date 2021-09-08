# ogma
Scripting language focused on processing tabular data.

# Release Process
---
When a release is ready, simply create a release tag and push it to Github.
The release workflow will take care of the build and release creation.
**The release body uses [RELEASE.md](./RELEASE.md) as the release notes.
Be sure to update this before the tag push!**

```
# Update RELEASE.md
git push
git tag v#.#
git push origin v#.#
```
