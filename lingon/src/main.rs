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
    let mut renderer = renderer::Renderer::new(&mut surface);
    let start_t = Instant::now();

    let rect = renderer::Rect::new();

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

        let rect = rect
            .angle(t)
            .r(t.sin())
            .g(t.sin());
        renderer.push(&rect);

        if renderer.render(&mut surface).is_err() {
            break 'app;
        }
    }
}
