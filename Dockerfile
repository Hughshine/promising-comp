FROM ubuntu:18.04
LABEL com.compoptcert.version="1.0"

RUN  apt-get update \
  && apt-get install -y wget make m4 build-essential patch unzip git libgmp3-dev \
  && rm -rf /var/lib/apt/lists/*

RUN wget https://github.com/ocaml/opam/releases/download/2.0.8/opam-2.0.8-x86_64-linux --no-check-certificate -O opam && \
    chmod 777 opam && \
    mv opam /usr/local/bin/opam

RUN opam init -y --verbose --disable-sandboxing 

RUN test -r /root/.opam/opam-init/init.sh && . /root/.opam/opam-init/init.sh > /dev/null 2> /dev/null || true

RUN opam switch create compoptcert 4.11.0

RUN opam pin -y add coq 8.13.1

COPY . /compoptcert/

WORKDIR /compoptcert/

RUN ./configure
RUN eval $(opam env) && \
    make -j 

ENTRYPOINT ["bash"]
