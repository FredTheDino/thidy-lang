in vec4 v_color;
in vec3 v_uv;

uniform sampler3D tex;

out vec4 frag_color;

void main() {
    if (v_uv.z < 0) {
        frag_color = v_color;
    } else {
        frag_color = (v_color * texture(tex, v_uv));
    }
}
