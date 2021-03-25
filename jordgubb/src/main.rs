// use glfw::{Action, Context as _, Key, WindowEvent};
use luminance_sdl2::{GL33Surface, sdl2};
use luminance_windowing::{WindowDim, WindowOpt};
use std::process::exit;
use luminance::context::GraphicsContext;
use luminance::pipeline::PipelineState;
use std::time::Instant;
use luminance_derive::{Semantics, Vertex, UniformInterface};
use luminance::tess::Mode;
use luminance::render_state::RenderState;
use luminance::shader::Uniform;

#[derive(Copy, Clone, Debug, Semantics)]
pub enum VertexSemantics {
    #[sem(name = "position", repr = "[f32; 2]", wrapper = "VertexPosition")]
    Position,
    #[sem(name = "color", repr = "[u8; 3]", wrapper = "VertexRGB")]
    Color,
}

#[derive(Vertex, Copy, Clone)]
#[vertex(sem = "VertexSemantics")]
pub struct Vertex {
    position: VertexPosition,

    #[vertex(normalized = "true")]
    color: VertexRGB,
}

#[derive(Debug, UniformInterface)]
pub struct ShaderInterface {
    #[uniform(unbound)]
    t: Uniform<f32>,
}


fn main() {
    let surface = GL33Surface::build_with(|video| video.window("game", 800, 600))
        .expect("Failed to create surface");

    main_loop(surface);
}

const VERTICES: [Vertex; 3] = [
    Vertex::new(
        VertexPosition::new([-0.5, -0.5]),
        VertexRGB::new([255, 0, 0]),
    ),
    Vertex::new(
        VertexPosition::new([0.5, -0.5]),
        VertexRGB::new([0, 255, 0]),
    ),
    Vertex::new(
        VertexPosition::new([0., 0.5]),
        VertexRGB::new([0, 0, 255]),
    ),
];
const VS_STR: &str = include_str!("vs.glsl");
const FS_STR: &str = include_str!("fs.glsl");

fn main_loop(mut surface: GL33Surface) {
    let start_t = Instant::now();
    let back_buffer = surface.back_buffer().unwrap();

    let mut program = surface
        .new_shader_program::<VertexSemantics, (), ShaderInterface>()
        .from_strings(VS_STR, None, None, FS_STR)
        .unwrap()
        .ignore_warnings();

    'app: loop {
        for event in surface.sdl().event_pump().unwrap().poll_iter() {
            use sdl2::event::{Event, WindowEvent};
            use sdl2::keyboard::Keycode;
            match event {
                Event::Quit { .. } => {
                    break 'app;
                }
                Event::Window { win_event:WindowEvent::Close, .. } => {
                    break 'app;
                }
                Event::KeyUp { keycode:Some(Keycode::Escape), .. } => {
                    break 'app;
                }
                _ => {}
            }
        }

        let triangle = surface
            .new_tess()
            .set_vertices(&VERTICES[..])
            .set_mode(Mode::Triangle)
            .build()
            .unwrap();

        let t = start_t.elapsed().as_millis() as f32 * 1e-3;
        let color = [t.cos(), t.sin(), 0.5, 1.];

        let render = surface.new_pipeline_gate().pipeline(
            &back_buffer,
            &PipelineState::default().set_clear_color(color),
            |_, mut shd_gate| {
                shd_gate.shade(&mut program, |mut iface, uni, mut rdr_gate| {
                    iface.set(&uni.t, t);

                    rdr_gate.render(&RenderState::default(), |mut tess_gate| {
                        tess_gate.render(&triangle)
                    })
                })
            },
        ).assume();

        if render.is_ok() {
            surface.window().gl_swap_window();
        } else {
            break 'app;
        }
    }
}
