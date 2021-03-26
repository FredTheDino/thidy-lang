out vec4 frag_color;

uniform sampler3D tex;

in vec4 v_color;

void main() {
    frag_color = vec4(v_color.xyz, texture(tex, vec3(0.0, 0.0, 0.0)) * 0.1 + 1.0);
}
