uniform float t;
in vec2 co;

in float spawn;
in float lifetime;

in vec2 position;
in vec2 velocity;
in vec2 acceleration;
in float drag;

in vec3 angle_info;

in vec4 scale_extreems;

in vec4 start_color;
in vec4 end_color;

out vec4 v_color;
out vec3 v_uv;
out int v_sheet;

vec2 rotate(vec2 p, float angle) {
    return vec2(p.x * cos(angle) - p.y * sin(angle),
                p.x * sin(angle) + p.y * cos(angle));
}

void main() {
    float l = t - spawn;
    float drag_sum = (1.0 - exp(-l * drag)) / drag;
    vec2 p = position + (velocity + acceleration * l) * drag_sum;

    float angle = angle_info.x;
    float angle_velocity = angle_info.y;
    float angle_drag = angle_info.z;
    float angle_drag_sum = (1.0 - exp(-l * angle_drag)) / angle_drag;
    float a = angle + angle_velocity * angle_drag_sum;

    float lerp = min(1.0, l / lifetime);
    v_color = mix(start_color, end_color, lerp) + vec4(0.0, 1.0, 0.0, 1.0);
    vec2 s = mix(scale_extreems.xy, scale_extreems.zw, lerp) + vec2(0.1, 0.1);

    gl_Position = vec4(rotate(co * s, a) + p, 0.0, 1.0);
}
