# Contributions
Pull requests are appreciated and encouraged! The request will be subject to a review and will 
need to pass the CI before being merged in. Please ensure:
- Tests are added where necessary,
- `cargo fmt --all -- --check` passes,
- `cargo clippy --workspace -- -D warnings` passes,
- `cargo test --workspace` passes,
- An item describing your pull request is added to [RELEASE.md](./RELEASE.md).

If you would like to become an administrator of the repository, please contact us directly for discussion.

Happy coding!

# Release Process

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
