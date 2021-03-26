

pub fn main() {
    let context = init();
    loop {
        context.input.poll();
        context.input.is_down(Input::Left);

        // update
        // Not relevant right now

        // Sprites
        // A sprite is:
        //  - slot, left, top, right, bottom in UV space
        //  Uploads the texture imediately
        //
        //  Hide files, so cache the relevant information.
        let sprites = SpriteSheet::new("file.png", context)
            .tile_size(16, 16) // 16x16 tiles

        let a = sprites.tile(x, y);
        let specific = sprites.sprite(0, 0, 16, 8) // Sprite at (0, 0) -> (16, 8), bx, by, fx, fy

        // draw
        context.gfx.sprite(id, (x, y), r, (sx, sy), (r, g, b, a));

        // Trait transform? Can be moved around?

        context.camera
            .at(x, y)
            // .move(dx, dy) OwO - I like this
            .zoom(zoom)
            .rotate(r)

        // A graphics object without a sprite
        context.gfx.push(Rect::new()
            .at(x, y)
            .rotate(r)
            .scale(sx, sy)
            .tint(r, g, b, a)
        );


        let id = sprites.get(1, 2);
        // Sprite is copy?
        // Layers and draw order!
        // Trait `drawable`!
        context.gfx.push(Sprite::new(id)
            .at(x, y)
            .rotate(r)
            .scale(sx, sy)
            .tint(r, g, b, a)
        );

        context.gfx.push_layer(Sprite::new(id)
            .at(x, y)
            .rotate(r)
            .scale(sx, sy)
            .tint(r, g, b, a)
        , z);

        // Simulate on GPU, only give a t?
        // time
        // ..., spawn
        //
        let system = ParticleSystem::new(max_num)
            .sprites(&[a, b, c, d])
            .gravity(gx, gy)
            .drag(d)
            .at(p)
            .dettach() // Particles move seperate from the system
            .attatch() // Partivles move with the system
            // Macro to genrate these? :o
            .lifetime(&[lo, hi], Distribution::Linear)
            .dx_range(&[lo, hi], Distribution::Linear)
            .dy_range(&[lo, hi], Distribution::Quadratic)
            .vx_range(&[lo, hi], Distribution::Linear)
            .vy_range(&[lo, hi], Distribution::Quadratic)
            .sx_range(&[lo, hi], Distribution::Linear)
            .sy_range(&[lo, hi], Distribution::Linear)
            .alpha(start_lo, start_hi, Distribution::Linear,
                   Interpelation::Linear,
                   end_lo, end_hi, Distribution::Linear)

        // Fixed step?
        system.update(delta);

        // Borrowed until rendering? Copied in? Requires a clone?
        context.gfx.push(&system);

        context.gfx.render();
    }
}
