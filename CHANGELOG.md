* 0.7.4 - October 28, 2023

    - Increased MSRV to 1.65, got it wrong last time because I forgot to check
      the `arc` feature.

* 0.7.3 - October 28, 2023

    - Made `Copy` and `Clone` for ArenaIntern support `?Sized` types.

* 0.7.2 - October 28, 2023

    - Increased MSRV to 1.60 for building and 1.65 for testing due to changes in
      dependencies.

    - Bumped ahash dependency version.

    - Optimization of `ArcInvtern` (thanks gwy15!).

* 0.7.1 - June 17, 2023

    - Added `ArcIntern::into_ref` (thanks PuzzleMaker!).

* 0.7.0 - March 30, 2022

    - Removed the `Borrow` implementation for interned types, which was not
      compliant with the documentation for that trait.  This did not lead to
      unsoundness, but did lead to confusing and buggy behavior.

    - Add new `Arena` type which can hold interned data that is then freed when
      the arena is dropped.

    - Renamed the intrinsic `from` method (which shadowed the `From` trait), so
      it would be easier and less  confusing to use `From` to create `Intern<T>`
      for `!Sized` types.

    - Added at least rudimentary support for common `!Sized` types, such as
      `Intern<str>`, `Intern<[u8]>` or `Intern<Path>`.  Please report any bugs
      you might encounter, as the test suite on such types is not fully
      populated.

* 0.6.0 - February 11, 2022

    - Removed `LocalIntern`, since I concluded that it was unsound.
      Specifically, since the order of dropping of thread-local storage is
      undefined, users could put a `LocalIntern` into thread-local storage, and
      get a use-after-free bug.

      I'm not sure that anyone ever used `LocalIntern`, and it wasn't faster
      than `Intern` anyhow (unlike what I documented and expected), so it's only
      advantage was that you could get a crude arena-storage-like effect by
      using `LocalIntern` within a temporary thread.  Not a very compelling use
      case.

    - Not an actual change, but I now use miri in the CI to check for undefined
      behavior, which is what clued me into the unsoundness in `LocalIntern`.