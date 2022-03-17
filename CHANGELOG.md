

* 0.7.0

    - Removed the `Borrow` implementation for interned types, which was not
      compliant with the documentation for that trait.  This did not lead to
      unsoundness, but did lead to confusing and buggy behavior.

    - Add new `Arena` type which can hold interned data that is then freed when
      the arena is dropped.  FIXME need to edit README

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