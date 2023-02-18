# Tutorial on Frama-C 

This is the (mostly .tex) source code for a small introduction tutorial on deductive program verficiation with [Frama-C](https://www.frama-c.com). 

## Download the pdf 

You can download the latest release of the tutorial [here](https://github.com/uu-1dt106/frama_c_tutorial/releases/latest/download/frama_c_tutorial.pdf)

## Building

In order to build the pdf locally, you can use docker

```sh
docker build -t frama_c_tutorial .
docker run --rm -v $PWD:/mnt -w /mnt frama_c_tutorial make
```

