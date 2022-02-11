

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