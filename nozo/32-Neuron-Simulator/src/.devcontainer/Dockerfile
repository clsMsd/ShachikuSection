FROM python:3

ENV DISPLAY host.docker.internal:0.0

RUN useradd -m neuron
USER neuron
ENV PATH $PATH:/home/neuron/.local/bin

RUN pip3 install neuron
