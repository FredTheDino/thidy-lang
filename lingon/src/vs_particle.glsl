uniform float t;
in vec2 co;

in float spawn;
in vec2 position;
in vec2 velocity;
in vec2 acceleration;
in float drag;

out vec4 v_color;
out vec3 v_uv;
out int v_sheet;

void main() {
    float l = t - spawn;
    float drag_sum = (1.0 - exp(-l * drag)) / drag;
    vec2 p = position + (velocity + acceleration * l) * drag_sum;

    gl_Position = vec4(co * drag * 0.1 + p, 0.0, 1.0);
}
