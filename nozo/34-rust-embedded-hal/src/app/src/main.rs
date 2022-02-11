#![no_std]
#![no_main]

use panic_halt as _;
use wio_terminal as wio;

use wio::entry;
use wio::pac::Peripherals;
use wio::prelude::*;

#[entry]
fn main() -> ! {
    let peripherals = Peripherals::take().unwrap();
    
    let pins = wio::Pins::new(peripherals.PORT);
    let mut user_led = pins.user_led.into_push_pull_output();
    user_led.set_high().unwrap();

    loop {}
}