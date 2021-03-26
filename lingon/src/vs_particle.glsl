uniform float t;
in vec2 co;

in float spawn;
in vec2 position;
in vec2 velocity;
in vec2 acceleration;

out vec4 v_color;
out vec3 v_uv;
out int v_sheet;

void main() {
    float l = t - spawn;
    vec2 p = position + velocity * l + acceleration * l * l / 2.0;

    gl_Position = vec4(co * 0.01 + p, 0.0, 1.0);
}
