let z;
//? {x = x && y = y}
function max(x: number, y: number) {
    if (x > y) {
        z = x;
    } else {}

    if (y > x) {
        z = y;
    } else {}
} //? {z >= y && z >= x && (z = x || z = y)}