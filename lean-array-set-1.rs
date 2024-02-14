#![allow(unused_mut)]


fn set_elements(mut arr: kani::array::Array<i32>, mut index:usize) -> kani::array::Array<i32> {
    if index < arr.len() {
        arr[index] = 1;
        return set_elements(arr, index+1);
    } else {
	return arr;
    }
}


pub fn set_one(mut arr: kani::array::Array<i32>) -> kani::array::Array<i32> {
    set_elements(arr, 0)
}
