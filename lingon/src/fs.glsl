// this was the vertex shader output; it’s now our (rasterized and interpolated) input!
in vec4 v_color;
in vec3 v_uv;

uniform sampler3D tex;

// we will output a single color
out vec4 frag_color;

void main() {
  // KISS
  frag_color = (v_color * texture(tex, v_uv));
}
