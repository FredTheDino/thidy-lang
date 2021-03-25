// those are our vertex attributes
in vec2 position;
in vec3 color;

uniform float t;

// this is the output of the vertex shader (we could have had several ones)
out vec3 v_color;

vec2 rotate(vec2 p, float angle) {
    return vec2(p.x * cos(angle) - p.y * sin(angle),
                p.x * sin(angle) + p.y * cos(angle));
}

void main() {
  // simply forward the color
  v_color = color * cos(t) * cos(t);

  // mandatory; tell the GPU to use the position vertex attribute to put the vertex in space
  gl_Position = vec4(rotate(position, t), 0., 1.);
}
