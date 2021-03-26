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

        renderer.push_instance(renderer::Instance::build(
            [t.sin() / ((t + 0.1) / 2.0), t.cos() / ((t + 0.1) / 2.0)],
            t,
            [t.sin(), (t + 1.0).sin()],
            [
                t.cos() * (t * 2.0).cos(),
                (t * 2.0).sin() * t.cos(),
                t / 100.0,
                1.0,
            ],
        ));

        renderer.push_instance(renderer::Instance::build(
            [t.sin() / ((t + 0.1) / 2.0), t.cos() / ((t + 0.1) / 2.0)],
            t,
            [t.cos(), (t + 1.0).cos()],
            [
                t.sin() * (t * 2.0).sin(),
                (t * 2.0).cos() * t.sin(),
                t / 100.0,
                1.0,
            ],
        ));

        if renderer.render(&mut surface).is_err() {
            break 'app;
        }
    }
}
