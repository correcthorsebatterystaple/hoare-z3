//? x = a AND y = b
function max(x: number, y: number, z: number) {
    if (x > y) {
        z = x;
    } else {
        z = y;
    }
} //? z >= a AND z >= b AND (z = a OR z = b)