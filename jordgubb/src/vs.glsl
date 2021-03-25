in vec2 co;

in vec2 position;
in float rotation;
in vec2 scale;
in vec4 color;

out vec4 v_color;

vec2 rotate(vec2 p, float angle) {
    return vec2(p.x * cos(angle) - p.y * sin(angle),
                p.x * sin(angle) + p.y * cos(angle));
}

void main() {
  v_color = color;

  gl_Position = vec4(rotate(co * scale, rotation) + position, 0., 1.);
  // gl_Position = vec4(co + position, 0., 1.);
}
