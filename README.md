# Checking the formal development 

We provide a Docker [1] image that contains a ready to use EasyCrypt
installation along with a copy of the EasyCrypt formal
development. The Docker image has been tested on a X64_64 Linux & on
Apple M1 system (with Rosetta [2] configured so that X64_86 SMT provers
can be used).

[1] https://docs.docker.com/get-docker/
[2] https://en.wikipedia.org/wiki/Rosetta_(software)

To build the Docker image, run:

```shell
make build
```

You can then run EasyCrypt on the formal develoment by running:

```shell
make runtest
```

Please, ensure that your Docker installation allocates at least 2 cores
and 4GB of memory to the Docker instance.

To speed up the checking time, you can run several EasyCrypt instances
in parallel by running:

```shell
make JOBS=$n runtest
```

where $n is the number of parallel jobs. In that case, be sure that
you allocate enough resources to the Docker instance.
