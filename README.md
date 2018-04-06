This never really paid out all that well. It seems the GC overhead of smashing things in and out of the views wipes out almost all of the steady state storage benefits of having the Set stored more efficiently.

There are some papers that have also noted this same effect, using modules and view functions in ML the overhead of going through the views wipes out most if not all of the benefits of having more efficient internals.
