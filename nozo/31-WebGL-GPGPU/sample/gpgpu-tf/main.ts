window.onload = () => {
  const canvas = document.querySelector("#glCanvas");

  if (!(canvas instanceof HTMLCanvasElement)) {
    throw new Error("canvas not found");
  }

  const gl = canvas.getContext("webgl2");

  if (!gl) {
    throw new Error("fail to init WebGL");
  }

  const vsSource = `#version 300 es
    in float a;
    in float b;

    out float sum;
    out float diff;
    out float prod;

    void main(void){
      sum = a + b;
      diff = a - b;
      prod = a * b;
    }
    `;

  const fsSource = `#version 300 es
    precision highp float;

    void main(void){
    }
    `;

  const shaderProgram = initShaderProgram(gl, vsSource, fsSource, [
    "sum",
    "diff",
    "prod",
  ]);

  if (!shaderProgram) {
    throw new Error("fail to init shaderProgram");
  }

  const aLoc = gl.getAttribLocation(shaderProgram, "a");
  const bLoc = gl.getAttribLocation(shaderProgram, "b");

  const a = [1, 2, 3, 4, 5, 6];
  const b = [3, 6, 9, 12, 15, 18];

  const attrs = [
    { buffer: a, index: aLoc, size: 1 },
    { buffer: b, index: bLoc, size: 1 },
  ];

  const vao = create_vao(gl, attrs, []);

  const tf = gl.createTransformFeedback();
  gl.bindTransformFeedback(gl.TRANSFORM_FEEDBACK, tf);

  const sumBuf = makeBuffer(gl, a.length * 4);
  const diffBuf = makeBuffer(gl, a.length * 4);
  const prodBuf = makeBuffer(gl, a.length * 4);
  gl.bindBufferBase(gl.TRANSFORM_FEEDBACK_BUFFER, 0, sumBuf);
  gl.bindBufferBase(gl.TRANSFORM_FEEDBACK_BUFFER, 1, diffBuf);
  gl.bindBufferBase(gl.TRANSFORM_FEEDBACK_BUFFER, 2, prodBuf);

  gl.bindTransformFeedback(gl.TRANSFORM_FEEDBACK, null);
  gl.bindBuffer(gl.ARRAY_BUFFER, null);

  // render
  gl.bindVertexArray(vao);
  gl.enable(gl.RASTERIZER_DISCARD);

  gl.bindTransformFeedback(gl.TRANSFORM_FEEDBACK, tf);
  gl.beginTransformFeedback(gl.POINTS);
  gl.drawArrays(gl.POINTS, 0, a.length);
  gl.endTransformFeedback();
  gl.bindTransformFeedback(gl.TRANSFORM_FEEDBACK, null);

  gl.disable(gl.RASTERIZER_DISCARD);

  console.log(`a: ${a}`);
  console.log(`b: ${b}`);
  printResults(gl, sumBuf, "sumBuf");
  printResults(gl, diffBuf, "diffBuf");
  printResults(gl, prodBuf, "prodBuf");

  function printResults(
    gl: WebGL2RenderingContext,
    buffer: WebGLBuffer | null,
    label: string
  ) {
    const results = new Float32Array(a.length);
    gl.bindBuffer(gl.ARRAY_BUFFER, buffer);
    gl.getBufferSubData(gl.ARRAY_BUFFER, 0, results);
    console.log(`${label}: ${results}`);
  }

  function initShaderProgram(
    gl: WebGL2RenderingContext,
    vsSource: string,
    fsSource: string,
    varyings: string[]
  ): WebGLProgram | null {
    const vertexShader = loadShader(gl, gl.VERTEX_SHADER, vsSource);
    const fragmentShader = loadShader(gl, gl.FRAGMENT_SHADER, fsSource);

    if (!vertexShader || !fragmentShader) {
      return null;
    }

    const shaderProgram = gl.createProgram();

    if (!shaderProgram) {
      return null;
    }

    gl.attachShader(shaderProgram, vertexShader);
    gl.attachShader(shaderProgram, fragmentShader);

    if (varyings)
      gl.transformFeedbackVaryings(
        shaderProgram,
        varyings,
        gl.SEPARATE_ATTRIBS
      );

    gl.linkProgram(shaderProgram);

    if (!gl.getProgramParameter(shaderProgram, gl.LINK_STATUS)) {
      console.log(
        "Unable to initialize the shader program: ",
        gl.getProgramInfoLog(shaderProgram)
      );
      return null;
    }

    gl.useProgram(shaderProgram);

    return shaderProgram;
  }

  function loadShader(
    gl: WebGL2RenderingContext,
    type: number,
    source: string
  ): WebGLShader | null {
    const shader = gl.createShader(type);

    if (!shader) {
      console.log("An error occurred creating the shaders: ", type);
      return null;
    }

    gl.shaderSource(shader, source);
    gl.compileShader(shader);

    if (!gl.getShaderParameter(shader, gl.COMPILE_STATUS)) {
      console.log(
        "An error occurred compiling the shaders: ",
        gl.getShaderInfoLog(shader)
      );
      gl.deleteShader(shader);
      return null;
    }

    return shader;
  }

  function makeBuffer(
    gl: WebGL2RenderingContext,
    sizeOrData: any
  ): WebGLBuffer | null {
    const buf = gl.createBuffer();
    gl.bindBuffer(gl.ARRAY_BUFFER, buf);
    gl.bufferData(gl.ARRAY_BUFFER, sizeOrData, gl.STATIC_DRAW);
    return buf;
  }

  function create_vao(
    gl: WebGL2RenderingContext,
    attrs: {
      buffer: number[];
      index: number;
      size: number;
    }[],
    index_buffer: number[]
  ): WebGLVertexArrayObject | null {
    const vao = gl.createVertexArray();
    gl.bindVertexArray(vao);

    attrs.map((attr) => {
      const vbo = makeBuffer(gl, new Float32Array(attr.buffer));
      gl.enableVertexAttribArray(attr.index);
      gl.vertexAttribPointer(attr.index, attr.size, gl.FLOAT, false, 0, 0);
    });

    if (index_buffer) {
      const ibo = gl.createBuffer();
      gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, ibo);
      gl.bufferData(
        gl.ELEMENT_ARRAY_BUFFER,
        new Uint16Array(index_buffer),
        gl.STATIC_DRAW
      );
    }

    gl.bindVertexArray(null);
    return vao;
  }
};
