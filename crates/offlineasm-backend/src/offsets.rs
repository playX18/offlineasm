use crate::ast::Node;

pub fn offsets_list(ast: &Node) -> Vec<String> {
    let mut set = std::collections::BTreeSet::new();
    collect(ast, &mut set, Kind::Offset);
    set.into_iter().collect()
}

pub fn sizes_list(ast: &Node) -> Vec<String> {
    let mut set = std::collections::BTreeSet::new();
    collect(ast, &mut set, Kind::Size);
    set.into_iter().collect()
}

pub fn consts_list(ast: &Node) -> Vec<String> {
    let mut set = std::collections::BTreeSet::new();
    collect(ast, &mut set, Kind::Const);
    set.into_iter().collect()
}

enum Kind {
    Offset,
    Size,
    Const,
}

fn collect(node: &Node, out: &mut std::collections::BTreeSet<String>, kind: Kind) {
    match node {
        Node::StructOffset { .. } if matches!(kind, Kind::Offset) => {
            out.insert(node.dump());
        }
        Node::Sizeof { .. } if matches!(kind, Kind::Size) => {
            out.insert(node.dump());
        }
        Node::ConstExpr { .. } if matches!(kind, Kind::Const) => {
            out.insert(node.dump());
        }
        _ => {}
    }
    for child in node.children() {
        collect(
            child,
            out,
            match kind {
                Kind::Offset => Kind::Offset,
                Kind::Size => Kind::Size,
                Kind::Const => Kind::Const,
            },
        );
    }
}
