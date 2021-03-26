use luminance::context::GraphicsContext;
use luminance::pipeline::{PipelineState, TextureBinding};
use luminance::render_state::RenderState;
use luminance::shader::Uniform;
use luminance::texture::{Dim3, GenMipmaps, Sampler, Texture};
use luminance::pixel::{NormRGBA8UI, NormUnsigned};
use luminance::tess::Mode;
use luminance_derive::{Semantics, UniformInterface, Vertex};
use luminance_sdl2::GL33Surface;
use cgmath::Vector2;

#[derive(Debug, UniformInterface)]
pub struct ShaderInterface {
    #[uniform(unbound)]
    t: Uniform<f32>,

    tex: Uniform<TextureBinding<Dim3, NormUnsigned>>,
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
    #[sem(name = "sheet", repr = "f32", wrapper = "ISheet")]
    ISheet,
    #[sem(name = "uv", repr = "[f32; 4]", wrapper = "IUV")]
    IUV,
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
    pub sheet: ISheet,
    pub uv: IUV,
}

const VS_STR: &str = include_str!("vs.glsl");
const FS_STR: &str = include_str!("fs.glsl");
const SPRITESHEET_SIZE: [u32; 3] = [512, 512, 512];

const RECT: [Vertex; 6] = [
    Vertex::new(VPosition::new([-0.5, -0.5])),
    Vertex::new(VPosition::new([0.5, -0.5])),
    Vertex::new(VPosition::new([0.5, 0.5])),
    Vertex::new(VPosition::new([0.5, 0.5])),
    Vertex::new(VPosition::new([-0.5, 0.5])),
    Vertex::new(VPosition::new([-0.5, -0.5])),
];

#[derive(Clone, Debug)]
pub struct SpriteSheetBuilder {
    pub image: Vec<u8>,
    pub image_dim: (usize, usize),
    pub tile_dim: Option<(usize, usize)>,
}

impl SpriteSheetBuilder {
    pub fn new(width: usize, height: usize, image: Vec<u8>) -> Self {
        Self {
            image,
            image_dim: (width, height),
            tile_dim: None,
        }
    }

    pub fn tile_size(mut self, tile_width: usize, tile_height: usize) -> Self {
        self.tile_dim = Some((tile_width, tile_height));
        self
    }
}


#[derive(Clone, Copy, Debug)]
pub struct SpriteSheet {
    id: usize,
    image_dim: (usize, usize),
    tile_dim: Option<(usize, usize)>,
}

impl SpriteSheet {
    pub fn grid(&self, tx: usize, ty: usize) -> SpriteRegion {
        if let Some(tile_dim) = self.tile_dim {
            let xlo = ((tile_dim.0 * tx) as f32) / (SPRITESHEET_SIZE[0] as f32);
            let ylo = ((tile_dim.1 * ty) as f32) / (SPRITESHEET_SIZE[1] as f32);
            let w = (tile_dim.0 as f32) / (SPRITESHEET_SIZE[0] as f32);
            let h = (tile_dim.1 as f32) / (SPRITESHEET_SIZE[1] as f32);
            (self.id as f32 / (SPRITESHEET_SIZE[2] as f32), [xlo, ylo, xlo + w, ylo + h])
        } else {
            panic!();
        }
    }
}

pub type Tex = Texture<<GL33Surface as GraphicsContext>::Backend, Dim3, NormRGBA8UI>;
pub type RenderFn = dyn FnMut(&[Instance], &mut Tex, &mut GL33Surface) -> Result<(), ()>;

pub struct Renderer {
    render_fn: Box<RenderFn>,
    instances: Vec<Instance>,
    tex: Tex,
    sprite_sheets: Vec<SpriteSheet>,
}

pub trait Transform {
    fn x_mut(&mut self) -> &mut f32;
    fn y_mut(&mut self) -> &mut f32;

    fn sx_mut(&mut self) -> &mut f32;
    fn sy_mut(&mut self) -> &mut f32;

    fn r_mut(&mut self) -> &mut f32;

    fn color_mut(&mut self) -> &mut [f32; 4];

    // TODO(ed): Move these to some form of macro?
    fn move_by(&mut self, x: f32, y: f32) -> &mut Self {
        *self.x_mut() += x;
        *self.y_mut() += y;
        self
    }

    fn at(&mut self, x: f32, y: f32) -> &mut Self {
        *self.x_mut() = x;
        *self.y_mut() = y;
        self
    }

    fn angle(&mut self, angle: f32) -> &mut Self {
        *self.r_mut() = angle;
        self
    }

    fn rotate(&mut self, angle: f32) -> &mut Self {
        *self.r_mut() += angle;
        self
    }

    fn scale(&mut self, sx: f32, sy: f32) -> &mut Self {
        *self.sx_mut() *= sx;
        *self.sy_mut() *= sy;
        self
    }

    fn rgb(&mut self, r: f32, g: f32, b: f32) -> &mut Self {
        self.color_mut()[0] = r;
        self.color_mut()[1] = g;
        self.color_mut()[2] = b;
        self
    }

    fn rgba(&mut self, r: f32, g: f32, b: f32, a: f32) -> &mut Self {
        self.color_mut()[0] *= r;
        self.color_mut()[1] *= g;
        self.color_mut()[2] *= b;
        self.color_mut()[3] *= a;
        self
    }

    fn r(&mut self, r: f32) -> &mut Self {
        self.color_mut()[0] *= r;
        self
    }

    fn g(&mut self, g: f32) -> &mut Self {
        self.color_mut()[1] *= g;
        self
    }

    fn b(&mut self, b: f32) -> &mut Self {
        self.color_mut()[2] *= b;
        self
    }

    fn a(&mut self, a: f32) -> &mut Self {
        self.color_mut()[3] *= a;
        self
    }
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
        &mut self.scale.x
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
        Instance {
            position: IPosition::new(self.position.into()),
            rotation: IRotation::new(self.rotation),
            scale: IScale::new(self.scale.into()),
            color: IColor::new(self.color),
            sheet: ISheet::new(0.0),
            uv: IUV::new([0.0, 0.0, 1.0, 1.0]),
        }
    }
}

impl Stamp for Rect {
    fn stamp(self) -> Instance {
        (&self).stamp()
    }
}

// TODO(ed): This feels dumb...
impl Stamp for &mut Rect {
    fn stamp(self) -> Instance {
        (*self).stamp()
    }
}

#[allow(dead_code)]
impl Rect {
    pub fn new() -> Self {
        Self {
            position: Vector2::new(0.0, 0.0),
            scale: Vector2::new(1.0, 1.0),
            rotation: 0.0,
            color: [1.0, 1.0, 1.0, 1.0],
        }
    }

}

#[derive(Clone, Copy, Debug)]
pub struct Sprite {
    position: Vector2<f32>,
    scale: Vector2<f32>,
    rotation: f32,
    color: [f32; 4],
    sheet: f32,
    rect: [f32; 4],
}

impl Transform for Sprite {
    fn x_mut(&mut self) -> &mut f32 {
        &mut self.position.x
    }
    fn y_mut(&mut self) -> &mut f32 {
        &mut self.position.y
    }

    fn sx_mut(&mut self) -> &mut f32 {
        &mut self.scale.x
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

impl Stamp for &Sprite {
    fn stamp(self) -> Instance {
        Instance {
            position: IPosition::new(self.position.into()),
            rotation: IRotation::new(self.rotation),
            scale: IScale::new(self.scale.into()),
            color: IColor::new(self.color),
            sheet: ISheet::new(self.sheet),
            uv: IUV::new(self.rect),
        }
    }
}

impl Stamp for Sprite {
    fn stamp(self) -> Instance {
        (&self).stamp()
    }
}

impl Stamp for &mut Sprite {
    fn stamp(self) -> Instance {
        (*self).stamp()
    }
}

type SpriteRegion = (f32, [f32; 4]);

#[allow(dead_code)]
impl Sprite {
    pub fn new(region: SpriteRegion) -> Self {
        Self {
            position: Vector2::new(0.0, 0.0),
            scale: Vector2::new(1.0, 1.0),
            rotation: 0.0,
            color: [1.0, 1.0, 1.0, 1.0],
            sheet: region.0,
            rect: region.1,
        }
    }
}

pub fn load_image_from_memory(bytes: &[u8]) -> (u32, u32, Vec<u8>) {
    unsafe {
        use stb_image::stb_image::bindgen::*;
        stbi_set_flip_vertically_on_load(1);
        let mut w: i32 = 0;
        let mut h: i32 = 0;
        let mut comp: i32 = 4;
        let image = stbi_load_from_memory(
            bytes.as_ptr(),
            bytes.len() as i32,
            &mut w,
            &mut h,
            &mut comp,
            4
        );
        let image = Vec::from_raw_parts(image as *mut u8, (w * h * 4) as usize, (w * h * 4) as usize);
        (w as u32, h as u32, image)
    }
}


impl Renderer {
    pub fn new(context: &mut GL33Surface, sampler: Sampler) -> Self {
        let back_buffer = context.back_buffer().unwrap();
        let mut program = context
            .new_shader_program::<VertexSemantics, (), ShaderInterface>()
            .from_strings(VS_STR, None, None, FS_STR)
            .unwrap()
            .ignore_warnings();


        let tex: Tex = Texture::new(context, SPRITESHEET_SIZE, 0, sampler)
            .expect("texture createtion!");

        let render_fn = move |
            instances: &[Instance],
            tex: &mut Tex,
            context: &mut GL33Surface|
        {
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
                    |pipeline, mut shd_gate| {
                        let bound_tex = pipeline.bind_texture(tex)?;

                        let state = RenderState::default().set_depth_test(None);
                        shd_gate.shade(&mut program, |mut iface, uni, mut rdr_gate| {
                            iface.set(&uni.tex, bound_tex.binding());

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
            tex: tex,
            sprite_sheets: Vec::new(),
        }
    }

    pub fn push_instance(&mut self, instance: Instance) {
        self.instances.push(instance);
    }

    pub fn push<T: Stamp>(&mut self, stamp: T) {
        self.instances.push(stamp.stamp());
    }

    //    let image = include_bytes!("../res/coin.png");
    //    let (w, h, image) = load_image_from_memory(image);

    pub fn add_spritesheet(&mut self, builder: SpriteSheetBuilder) -> SpriteSheet {
        let id = self.sprite_sheets.len();
        assert!((id as u32) < SPRITESHEET_SIZE[2]);

        self.tex.upload_part_raw(GenMipmaps::No,
            [0, 0, id as u32],
            [builder.image_dim.0 as u32, builder.image_dim.1 as u32, 1],
            &builder.image).unwrap();
        // Upload texture to slot
        let sheet = SpriteSheet {
            id,
            image_dim: builder.image_dim,
            tile_dim: builder.tile_dim,
        };
        self.sprite_sheets.push(sheet);
        sheet
    }

    pub fn render(&mut self, context: &mut GL33Surface) -> Result<(), ()> {
        let res = (*self.render_fn)(&self.instances, &mut self.tex, context);
        self.instances.clear();
        res
    }
}
