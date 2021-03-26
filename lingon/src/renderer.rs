use luminance::context::GraphicsContext;
use luminance::pipeline::PipelineState;
use luminance::render_state::RenderState;
use luminance::shader::Uniform;
use luminance::tess::Mode;
use luminance_derive::{Semantics, UniformInterface, Vertex};
use luminance_sdl2::GL33Surface;
use cgmath::Vector2;

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

pub trait Transform {
    fn x_mut(&mut self) -> &mut f32;
    fn y_mut(&mut self) -> &mut f32;

    fn sx_mut(&mut self) -> &mut f32;
    fn sy_mut(&mut self) -> &mut f32;

    fn r_mut(&mut self) -> &mut f32;

    fn color_mut(&mut self) -> &mut [f32; 4];
}


pub trait Stamp {
    fn stamp(self) -> Instance;
}

#[derive(Clone, Copy, Debug)]
pub struct Rect {
    position: Vector2<f32>,
    scale: Vector2<f32>,
    rotation: f32,
    color: [f32; 4],
}

impl Transform for Rect {
    fn x_mut(&mut self) -> &mut f32 {
        &mut self.position.x
    }
    fn y_mut(&mut self) -> &mut f32 {
        &mut self.position.y
    }

    fn sx_mut(&mut self) -> &mut f32 {
        &mut self.scale.y
    }
    fn sy_mut(&mut self) -> &mut f32 {
        &mut self.scale.y
    }

    fn r_mut(&mut self) -> &mut f32 {
        &mut self.rotation
    }

    fn color_mut(&mut self) -> &mut [f32; 4] {
        &mut self.color
    }
}

impl Stamp for &Rect {
    fn stamp(self) -> Instance {
        Instance::build(
            self.position.into(),
            self.rotation,
            self.scale.into(),
            self.color,
        )
    }
}

impl Stamp for Rect {
    fn stamp(self) -> Instance {
        (&self).stamp()
    }
}


impl Rect {
    pub fn new() -> Self {
        Self {
            position: Vector2::new(0.0, 0.0),
            scale: Vector2::new(1.0, 1.0),
            rotation: 0.0,
            color: [1.0, 1.0, 1.0, 1.0],
        }
    }

    pub fn move_by(mut self, x: f32, y: f32) -> Self {
        *self.x_mut() += x;
        *self.y_mut() += y;
        self
    }

    pub fn at(mut self, x: f32, y: f32) -> Self {
        *self.x_mut() = x;
        *self.y_mut() = y;
        self
    }

    pub fn angle(mut self, angle: f32) -> Self {
        *self.r_mut() = angle;
        self
    }

    pub fn rotate(mut self, angle: f32) -> Self {
        *self.r_mut() += angle;
        self
    }

    pub fn scale(mut self, sx: f32, sy: f32) -> Self {
        *self.sx_mut() *= sx;
        *self.sy_mut() *= sy;
        self
    }

    pub fn rgb(mut self, r: f32, g: f32, b: f32) -> Self {
        self.color_mut()[0] = r;
        self.color_mut()[1] = g;
        self.color_mut()[2] = b;
        self
    }

    pub fn rgba(mut self, r: f32, g: f32, b: f32, a: f32) -> Self {
        self.color_mut()[0] *= r;
        self.color_mut()[1] *= g;
        self.color_mut()[2] *= b;
        self.color_mut()[3] *= a;
        self
    }

    pub fn r(mut self, r: f32) -> Self {
        self.color_mut()[0] *= r;
        self
    }

    pub fn g(mut self, g: f32) -> Self {
        self.color_mut()[1] *= g;
        self
    }

    pub fn b(mut self, b: f32) -> Self {
        self.color_mut()[2] *= b;
        self
    }

    pub fn a(mut self, a: f32) -> Self {
        self.color_mut()[3] *= a;
        self
    }
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

    pub fn push<T: Stamp>(&mut self, stamp: T) {
        self.instances.push(stamp.stamp());
    }

    pub fn render(&mut self, context: &mut GL33Surface) -> Result<(), ()> {
        let res = (*self.render_fn)(&self.instances, context);
        self.instances.clear();
        res
    }
}
