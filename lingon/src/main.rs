// use glfw::{Action, Context as _, Key, WindowEvent};
use luminance_sdl2::{sdl2, GL33Surface};
use std::time::Instant;

// TODO(ed):
//  - Upload textures
//  - Send texture coordinates
//  - Write the API. :)

mod renderer;

fn main() {
    let surface = GL33Surface::build_with(|video| video.window("game", 800, 600))
        .expect("Failed to create surface");

    main_loop(surface);
}

fn main_loop(mut surface: GL33Surface) {
    use renderer::*;
    let mut sampler = luminance::texture::Sampler::default();
    sampler.mag_filter = luminance::texture::MagFilter::Nearest;
    let mut renderer = Renderer::new(&mut surface, sampler);

    let (w, h, image) = load_image_from_memory(include_bytes!("../res/coin.png"));
    let builder = SpriteSheetBuilder::new(w as usize, h as usize, image).tile_size(16, 16);
    let sheet = renderer.add_spritesheet(builder);

    let start_t = Instant::now();

    'app: loop {
        let t = start_t.elapsed().as_millis() as f32 * 1e-3;

        for event in surface.sdl().event_pump().unwrap().poll_iter() {
            use sdl2::event::{Event, WindowEvent};
            use sdl2::keyboard::Keycode;
            match event {
                Event::Quit { .. } => {
                    break 'app;
                }
                Event::Window {
                    win_event: WindowEvent::Close,
                    ..
                } => {
                    break 'app;
                }
                Event::KeyDown {
                    keycode: Some(Keycode::Escape),
                    ..
                } => {
                    break 'app;
                }
                _ => {}
            }
        }

        renderer.push(Rect::new()
            .scale(0.3, 0.3)
            .move_by(-0.3, 0.0)
            .angle(t)
            .r(t.sin())
            .g(t.sin()));

        let region = sheet.grid([0, 1, 2, 3, 2, 1][((t * 10.0) as usize) % 6], 0);
        renderer.push(Sprite::new(region)
            .scale(0.3, 0.3)
            .move_by(0.3, 0.0)
            .angle(t));

        if renderer.render(&mut surface).is_err() {
            break 'app;
        }
    }
}
