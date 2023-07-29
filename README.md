# Bitssset
This is a compile-time sized bitset implementation that supports bitwise implementations, including shifts.

### Why another bitset implementation?
I built this to address a specific use-case that no other crate at the time could support.

Specifically I use this in my battlesnake AI [shapeshifter](https://github.com/JonathanArns/shapeshifter)
as the underlying datastructure for the bitboard representation of the game board.
For this I needed the bitset to be of arbitrary (but known at compile-time) size, so I can build
boards of different sizes and work with them without allocating heap memory and I needed fast
bitwise operations, Specifically including bit shifts.

This crate is production-tested in the sense that it powers one of the strongest multiplayer snake AIs
in the world. I still would advise against using it in other contexts, because it ditches some common
sense sanity checks around out of bounds access, which you would probably want to have in a more general
use-case.
