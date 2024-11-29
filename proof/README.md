> [!WARNING]  
> This proof is still work in progress.

# X-Wing Proof

This repository contains formally verified proofs of the game-based proofs presented in the [X-Wing paper](https://cic.iacr.org/p/1/1/21).

This proof has been tested using the 2024.09 version of Easycrypt.

## Proof structure

The proof has the following structure:

1. `KEM_ROM.ec` contains the abstract theory that defines a KEM and related security games, such as IND-CPA and IND-CCA. It then defines a concrete theory concerning KEMs in the ROM, and KEMs with two ROMs. The latter is required as the adversary will have access to two oracles in the X-Wing proof: an X-Wing decapsulation oracle, and the KEM oracle. This is because the KEM that X-Wing is instantiated with is proven to be secure in the ROM.
2. `NomGroup.eca` defines the abstract theory concerning nominal groups, and hence, X25519.
3. `PKE_ROM.ec` is similar to `KEM_ROM.c` in that it defines the abstract theory of PKEs and various security games for PKEs in and out of the ROM.
4. `ML-KEM-CCR.ec` proves the CCR security bound for ML-KEM.
5. `X-Wing-Classical.ec` proves the classical security bound for X-Wing.
6. `X-Wing-PQ.ec` proves the post-quantum security bound for X-Wing.

## Todos

To be filled out.


