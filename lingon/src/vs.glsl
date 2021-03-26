in vec2 co;

in vec2 position;
in float rotation;
in vec2 scale;
in vec4 color;
in float sheet;
in vec4 uv;

out vec4 v_color;
out vec3 v_uv;

vec2 rotate(vec2 p, float angle) {
    return vec2(p.x * cos(angle) - p.y * sin(angle),
                p.x * sin(angle) + p.y * cos(angle));
}

void main() {
  v_color = color;

  v_uv = vec3(
        mix(uv.x, uv.z, co.x + 0.5),
        mix(uv.y, uv.w, co.y + 0.5),
        sheet);

  gl_Position = vec4(rotate(co * scale, rotation) + position, 0., 1.);
}
