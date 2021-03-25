// use glfw::{Action, Context as _, Key, WindowEvent};
use luminance_sdl2::{GL33Surface, sdl2};
use luminance::context::GraphicsContext;
use luminance::pipeline::PipelineState;
use std::time::Instant;
use luminance_derive::{Semantics, Vertex, UniformInterface};
use luminance::tess::Mode;
use luminance::render_state::RenderState;
use luminance::shader::Uniform;

#[derive(Copy, Clone, Debug, Semantics)]
pub enum VertexSemantics {
    #[sem(name = "co", repr = "[f32; 2]", wrapper = "VPosition")]
    VPosition,

    #[sem(name = "position", repr = "[f32; 2]", wrapper = "IPosition")]
    IPosition,
    #[sem(name = "rotation", repr = "f32", wrapper = "IRotation")]
    IRotation,
    #[sem(name = "scale", repr = "[f32; 2]", wrapper = "IScale")]
    IScale,
    #[sem(name = "color", repr = "[f32; 4]", wrapper = "IColor")]
    IColor,
//    #[sem(name = "sprite", repr = "[f32; 5]", wrapper = "ISprite")]
//    ISprite,
}

#[repr(C)]
#[derive(Vertex, Copy, Clone, PartialEq)]
#[vertex(sem = "VertexSemantics")]
pub struct Vertex {
    pub position: VPosition,
}

#[repr(C)]
#[derive(Vertex, Copy, Clone, PartialEq)]
#[vertex(sem = "VertexSemantics", instanced = "true")]
pub struct Instance {
    pub position: IPosition,
    pub rotation: IRotation,
    pub scale: IScale,
    pub color: IColor,
    // sprite: ISprite,
}

impl Instance {
    fn build(position: [f32; 2],
             rotation: f32,
             scale: [f32; 2],
             color: [f32; 4],
             // sprite: [f32; 5]
    ) -> Self {
        Self {
            position: IPosition::new(position),
            rotation: IRotation::new(rotation),
            scale: IScale::new(scale),
            color: IColor::new(color),
            // sprite: ISprite::new(sprite),
        }
    }

    fn at(position: [f32; 2],
             rotation: f32,
    ) -> Self {
        Self::build(
            position,
            rotation,
            [1., 1.],
            [1., 1., 1., 1.],
            // [0., 0., 0., 0., 0.]
        )
    }
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

const RECT: [Vertex; 6] = [
    Vertex::new(
        VPosition::new([-0.5, -0.5]),
    ),
    Vertex::new(
        VPosition::new([0.5, -0.5]),
    ),
    Vertex::new(
        VPosition::new([0.5, 0.5]),
    ),
    Vertex::new(
        VPosition::new([0.5, 0.5]),
    ),
    Vertex::new(
        VPosition::new([-0.5, 0.5]),
    ),
    Vertex::new(
        VPosition::new([-0.5, -0.5]),
    ),
];


const VS_STR: &str = include_str!("vs.glsl");
const FS_STR: &str = include_str!("fs.glsl");

fn main_loop(mut surface: GL33Surface) {
    let start_t = Instant::now();
    let back_buffer = surface.back_buffer().unwrap();

    let mut program = surface
        .new_shader_program::<VertexSemantics, (), ()>()
        .from_strings(VS_STR, None, None, FS_STR)
        .unwrap()
        .ignore_warnings();


    let mut instances = Vec::new();

    'app: loop {
        let t = start_t.elapsed().as_millis() as f32 * 1e-3;

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
                Event::KeyDown { keycode:Some(Keycode::Escape), .. } => {
                    break 'app;
                }
                _ => {}
            }
        }

        instances.push(
            Instance::build(
                [t.sin() / ((t + 0.1) / 2.0), t.cos() / ((t + 0.1) / 2.0)],
                t,
                [t.sin(), (t + 1.0).sin()],
                [t.cos() * (t * 2.0).cos(), (t * 2.0).sin() * t.cos(), t / 100.0, 1.0]
            ));

        instances.push(
            Instance::build(
                [t.sin() / ((t + 0.1) / 2.0), t.cos() / ((t + 0.1) / 2.0)],
                t,
                [t.cos(), (t + 1.0).cos()],
                [t.sin() * (t * 2.0).sin(), (t * 2.0).cos() * t.sin(), t / 100.0, 1.0]
            ));

        if instances.len() % 100 == 0 {
            println!("Rendering: {}", instances.len());
        }


        let triangle = surface
            .new_tess()
            .set_vertices(&RECT[..])
            .set_instances(&instances[..])
            .set_mode(Mode::Triangle)
            .build()
            .unwrap();

        let render = surface
            .new_pipeline_gate()
            .pipeline(
                &back_buffer,
                &PipelineState::default(),
                |_, mut shd_gate| {
                    use luminance::blending::{Blending, Equation, Factor};
                    let state = RenderState::default()
                        .set_depth_test(None);
                    //    .set_blending(Some(Blending {
                    //    equation: Equation::Additive,
                    //    src: Factor::One,
                    //    dst: Factor::One,
                    //}));
                    shd_gate.shade(&mut program, |_, _, mut rdr_gate| {
                        rdr_gate.render(&state, |mut tess_gate| {
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
