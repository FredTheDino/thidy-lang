out vec4 frag_color;

uniform sampler3D tex;

void main() {
    frag_color = vec4(0.5, 0.0, 1.0, texture(tex, vec3(0.0, 0.0, 0.0)) * 0.1 + 1.0);
}
