use luminance::context::GraphicsContext;
use luminance::pipeline::PipelineState;
use luminance::render_state::RenderState;
use luminance::shader::Uniform;
use luminance::tess::Mode;
use luminance_derive::{Semantics, UniformInterface, Vertex};
use luminance_sdl2::GL33Surface;

#[derive(Debug, UniformInterface)]
pub struct ShaderInterface {
    #[uniform(unbound)]
    t: Uniform<f32>,
}

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
    pub fn build(
        position: [f32; 2],
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

    pub fn at(position: [f32; 2], rotation: f32) -> Self {
        Self::build(
            position,
            rotation,
            [1., 1.],
            [1., 1., 1., 1.],
            // [0., 0., 0., 0., 0.]
        )
    }
}

const VS_STR: &str = include_str!("vs.glsl");
const FS_STR: &str = include_str!("fs.glsl");

const RECT: [Vertex; 6] = [
    Vertex::new(VPosition::new([-0.5, -0.5])),
    Vertex::new(VPosition::new([0.5, -0.5])),
    Vertex::new(VPosition::new([0.5, 0.5])),
    Vertex::new(VPosition::new([0.5, 0.5])),
    Vertex::new(VPosition::new([-0.5, 0.5])),
    Vertex::new(VPosition::new([-0.5, -0.5])),
];

pub type RenderFn = dyn FnMut(&[Instance], &mut GL33Surface) -> Result<(), ()>;

pub struct Renderer {
    render_fn: Box<RenderFn>,
    instances: Vec<Instance>,
}

impl Renderer {
    pub fn new(context: &mut GL33Surface) -> Self {
        let back_buffer = context.back_buffer().unwrap();
        let mut program = context
            .new_shader_program::<VertexSemantics, (), ()>()
            .from_strings(VS_STR, None, None, FS_STR)
            .unwrap()
            .ignore_warnings();

        let render_fn = move |instances: &[Instance], context: &mut GL33Surface| {
            let triangle = context
                .new_tess()
                .set_vertices(&RECT[..])
                .set_instances(&instances[..])
                .set_mode(Mode::Triangle)
                .build()
                .unwrap();

            let render = context
                .new_pipeline_gate()
                .pipeline(
                    &back_buffer,
                    &PipelineState::default(),
                    |_, mut shd_gate| {
                        let state = RenderState::default().set_depth_test(None);
                        shd_gate.shade(&mut program, |_, _, mut rdr_gate| {
                            rdr_gate.render(&state, |mut tess_gate| tess_gate.render(&triangle))
                        })
                    },
                )
                .assume();

            if render.is_ok() {
                context.window().gl_swap_window();
                Ok(())
            } else {
                Err(())
            }
        };

        Self {
            render_fn: Box::new(render_fn),
            instances: Vec::new(),
        }
    }

    pub fn push_instance(&mut self, instance: Instance) {
        self.instances.push(instance);
    }

    pub fn render(&mut self, context: &mut GL33Surface) -> Result<(), ()> {
        let res = (*self.render_fn)(&self.instances, context);
        self.instances.clear();
        res
    }
}
