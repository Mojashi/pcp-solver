use pcp_solver::pcp::PCP;
use pcp_solver::{armc, pcp::unsolved_instances2};

fn main() {
    let pcp = PCP::parse_repr("11_1");
    let pcp = unsolved_instances2().get(2).unwrap().clone();
    let pcp = PCP::parse_repr("000_0__001_0__1_0011");
    let pcp = PCP::parse_repr("01_1__1_1101__111_1");
    let pcp = PCP::parse_repr("1111_1__1_1101__0_11"); //.co();
    println!("{:?}", pcp);

    armc::armc(pcp);
}
