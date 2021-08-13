window.onload = () => {
  const dstWidth = 3;
  const dstHeight = 2;
  const canvas = document.querySelector("#glCanvas");

  if (!(canvas instanceof HTMLCanvasElement)) {
    throw new Error("canvas not found");
  }
  canvas.width = dstWidth;
  canvas.height = dstHeight;

  const gl = canvas.getContext("webgl2");

  if (!gl) {
    throw new Error("fail to init WebGL");
  }

  const vsSource = `#version 300 es
    in vec4 position;

    void main(void){
        gl_Position = position;
    }
    `;

  const fsSource = `#version 300 es
    precision highp float;

    uniform sampler2D srcTex;

    out vec4 outColor;
    
    void main(void){
        ivec2 texelCoord = ivec2(gl_FragCoord.xy);
        vec4 value = texelFetch(srcTex, texelCoord, 0);
        outColor = value * 2.0;
    }
    `;

  const shaderProgram = initShaderProgram(gl, vsSource, fsSource);

  if (!shaderProgram) {
    throw new Error("fail to init shaderProgram");
  }

  // prettier-ignore
  const plane_pos = [
    -1, -1,
    -1,  1,
     1, -1,
     1, -1,
    -1,  1,
     1,  1
  ];

  const plane_attrs = [
    {
      buffer: plane_pos,
      index: gl.getAttribLocation(shaderProgram, "position"),
      size: 2,
    },
  ];

  const plane_vao = create_vao(gl, plane_attrs, []);
  gl.bindVertexArray(plane_vao);

  const srcWidth = 3;
  const srcHeight = 2;
  const tex = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, tex);
  gl.pixelStorei(gl.UNPACK_ALIGNMENT, 1);
  gl.texImage2D(
    gl.TEXTURE_2D,
    0,
    gl.R8,
    srcWidth,
    srcHeight,
    0,
    gl.RED,
    gl.UNSIGNED_BYTE,
    new Uint8Array([1, 2, 3, 4, 5, 6])
  );
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);

  gl.uniform1i(gl.getUniformLocation(shaderProgram, "srcTex"), 0);

  gl.drawArrays(gl.TRIANGLES, 0, plane_pos.length);

  const results = new Uint8Array(dstWidth * dstHeight * 4);
  gl.readPixels(0, 0, dstWidth, dstHeight, gl.RGBA, gl.UNSIGNED_BYTE, results);

  for (let i = 0; i < dstWidth * dstHeight; ++i) {
    console.log(i, results[i * 4]);
  }

  function initShaderProgram(
    gl: WebGL2RenderingContext,
    vsSource: string,
    fsSource: string
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
      const vbo = gl.createBuffer();
      gl.bindBuffer(gl.ARRAY_BUFFER, vbo);
      gl.bufferData(
        gl.ARRAY_BUFFER,
        new Float32Array(attr.buffer),
        gl.STATIC_DRAW
      );
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
