let z;
// {x = x && y = y}
function max(x: number, y: number) {
    if (x > y) {
        z = x;
    }

    if (y > x) {
        z = y;
    }
} // {z >= y && z >= x && (z = x || z = y)}