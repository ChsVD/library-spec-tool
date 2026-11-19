# Representation required by downstream proofs

For OpenSSL struct BIGNUM (bignum_st): find reference definitions describing a dynamic signed multiple-precision number, its backing limb array and which prefix is used. Need a connection between memory fields d (least-significant limb first), top (used length), dmax (allocated capacity), neg (sign), and the mathematical integer. Identify which fields, ownership and value interpretation the precedent actually supports and any layout adaptations.
The target function only reads the data pointer. Keep any representation facts beyond its body explicit as assumptions in its natural-language contract.
