use crate::pcp::PCP;

pub fn has_trivial_solution(pcp: &PCP) -> bool {
    pcp.tiles.iter().any(|tile| tile.up == tile.dn)
}
pub fn prefix_filter(pcp: &PCP, size: usize) -> bool {
    pcp.tiles.iter().any(|tile| tile.up.starts_with(&tile.dn) || tile.dn.starts_with(&tile.up))
}
pub fn postfix_filter(pcp: &PCP, size: usize) -> bool {
    pcp.tiles.iter().any(|tile| tile.up.ends_with(&tile.dn) || tile.dn.ends_with(&tile.up))
}
pub fn element_balance_filter(pcp: &PCP, size: usize) -> bool {
    pcp.tiles.iter().all(|tile| tile.up.len() == tile.dn.len())
}

// pub fn enumerate_nontrivial_instances(size: usize, width: usize) -> Vec<PCP> {
    
// }
