use pcp_solver::pcp::PCP;
use pcp_solver::proof::{Organizer, OrganizerImpl, ProverConfig};
use pcp_solver::infix_prefix_suffix_method::infix_prefix_suffix_method;

fn main() {
    let mut input = String::new();
    println!("Enter a PCP instance (e.g. '01_1__1_1101__111_1'):");

    std::io::stdin().read_line(&mut input).unwrap();
    let pcp = PCP::parse_repr(input.trim());

    println!("{:?}", pcp);
    
    match infix_prefix_suffix_method(pcp.clone()) {
        (true, depgrpah) => {
            println!("true");
            let pcp_str = pcp.repr();
            let dir = format!("pcpproof/{}", pcp_str);
            let o: &mut dyn Organizer = &mut OrganizerImpl::new(ProverConfig::default());
            println!("dir: {}", dir);

            o.proof_has_no_solution_eff(pcp.clone(), &depgrpah); //, &depgrpah.shrink_to_one_node(&pcp));
            o.save_all(&format!("PCPProof_{}", pcp.repr()), &dir, "proof/pcplib")
        }
        (false, _) => println!("false"),
    }
}
