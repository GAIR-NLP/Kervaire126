'use strict';

// Mathematical dependency edges from the native project export.
function moduleDependencies(project, modules) {
  const names = new Set(modules.map(module => module.id));
  const statements = new Map(project.entries.map(entry => [entry.id, entry]));
  const chapterOwners = new Map(project.chapters.map(chapter =>
    [chapter.title, modules[Number(chapter.num) - 1]?.id]));
  const owner = entry => chapterOwners.get(entry?.chapter);
  const pairs = new Map();
  for (const consumer of project.entries) {
    const to = owner(consumer);
    if (!names.has(to)) continue;
    for (const dependency of consumer.deps || []) {
      if (dependency.type !== 'uses') continue;
      const from = owner(statements.get(dependency.id));
      if (!names.has(from) || from === to) continue;
      if (!pairs.has(from + ':' + to)) {
        pairs.set(from + ':' + to, {from, to, witness: statements.get(dependency.id).title});
      }
    }
  }
  const order = new Map(modules.map((module, index) => [module.id, index]));
  return [...pairs.values()].sort((a, b) => order.get(a.from) - order.get(b.from) || order.get(a.to) - order.get(b.to));
}


function statementAliases(project) {
  const byId = new Map(project.entries.map(entry => [entry.id, entry]));
  const statements = new Map(project.entries.map(entry => [entry.label, entry]));
  for (const [label, reference] of Object.entries(project.refs || {})) {
    if (reference.kind === 'stmt' && byId.has(reference.id)) {
      statements.set(label, byId.get(reference.id));
    }
  }
  return statements;
}

// Descriptions of cross-chapter dependency edges.
function handoffDescription(edge) {
  const descriptions = {
    'SpectralSequence:AdamsSynthetic': 'Extension spectral sequences.',
    'SpectralSequence:Literature': 'Filtration, associated graded objects and boundedness.',
    'SpectralSequence:AdamsComputation': 'Labeled differentials and their targets.',
    'SpectralSequence:ProofTools': 'Filtration, associated graded objects and boundedness.',
    'SpectralSequence:SSComputation': 'Finite windows and permanent cycles.',
    'SpectralSequence:Main': 'Detection and changes of filtration.',
    'AdamsSynthetic:Literature': 'The synthetic analogue functor.',
    'AdamsSynthetic:AdamsComputation': 'The sphere second-page algebra.',
    'AdamsSynthetic:ProofTools': 'Convergence on the specified object families.',
    'AdamsSynthetic:SSComputation': 'Standard sphere classes.',
    'AdamsSynthetic:Main': 'Support and separation for finite spectra.',
    'Literature:AdamsComputation': 'Classical classes detected by g and Δh₁g.',
    'Literature:ProofTools': 'Infinity pages of finite λ quotients.',
    'AdamsComputation:ProofTools': 'E₂ coordinates and algebra.',
    'AdamsComputation:SSComputation': 'E₂ bases, products and initial computation inputs.',
    'AdamsComputation:Main': 'Product identities, vanishing and degree constraints.',
    'ProofTools:Main': 'Extension equations and representative comparisons.',
    'SSComputation:Main': 'Differentials, boundaries and survival on the actual pages.',
    'Literature:SSComputation': 'Known differentials and detection comparisons.',
    'Literature:Main': 'Detection criteria and total-boundary inputs; tmf vanishing in stem 62 and low filtration, and the specified stem-125 image not annihilated by odd integers, for high-filtration detection.',
    'Literature:Geometry': 'Browder’s criterion, geometric inputs and high-dimensional nonexistence.',
    'Main:Geometry': 'Nonzero permanent survival of the standard square h₆².',
  };
  return descriptions[edge.from + ':' + edge.to]
    || 'Specified input: ' + edge.witness.replace(/\$/g, '').replace(/h_6\^2/g, 'h₆²');
}

// Route dependency edges through free space between the cards.
function routeModuleEdges(edges, boxes, width, height, labelBoxes, minX = 0) {
  const inset = 8;
  const order = new Map([...boxes.keys()].map((id, index) => [id, index]));
  const obstacles = [...boxes.values(), ...labelBoxes].map(box => ({
    left: box.left - inset, right: box.right + inset,
    top: box.top - inset, bottom: box.bottom + inset,
  }));
  const round = value => Math.round(value * 1000) / 1000;
  const xs = new Set([minX + 4, width - 4]);
  const ys = new Set([4, height - 4]);
  for (const box of obstacles) {
    xs.add(box.left - 3); xs.add(box.right + 3);
    ys.add(box.top - 3); ys.add(box.bottom + 3);
  }
  // Parallel lanes in the central gutter keep long computation outputs away
  // from both intermediate cards and the external-program input arrows.
  const rows = new Map();
  for (const box of boxes.values()) {
    const key = Math.round(box.top);
    if (!rows.has(key)) rows.set(key, []);
    rows.get(key).push(box);
  }
  for (const row of rows.values()) {
    row.sort((a, b) => a.left - b.left);
    for (let i = 1; i < row.length; i++) {
      const middle = (row[i - 1].right + row[i].left) / 2;
      for (const offset of [-10, 0, 10]) xs.add(middle + offset);
    }
  }
  const endpoints = new Map();
  const routes = new Map();
  const segments = [];
  const key = edge => edge.from + ':' + edge.to;
  const sameRow = edge => Math.abs(boxes.get(edge.from).top - boxes.get(edge.to).top) < 2;
  const computation = edge => ['AdamsComputation', 'SSComputation'].includes(edge.from);
  const longEdge = edge => {
    const from=boxes.get(edge.from), to=boxes.get(edge.to);
    return to.stage-from.stage>1 || labelBoxes.some(box => box.height>100
      && box.top>=from.bottom && box.bottom<=to.top);
  };
  const right = Math.max(...[...boxes.values(), ...labelBoxes].map(box => box.right));
  // Long dependencies share a source's outside lane. Their vertical sections
  // always stay beyond every card and expanded detail panel, within the map.
  const longSources = [...new Set(edges.filter(longEdge).map(edge => edge.from))]
    .sort((a, b) => order.get(a) - order.get(b));
  const laneGap=Math.min(8, (width-right-24)/Math.max(1,longSources.length-1));
  const rightLanes = new Map(longSources.map((id, index) =>
    [id, round(right + 16 + (longSources.length - 1 - index) * laneGap)]));
  function retain(edge, points, rightSide=false) {
    const compact = [];
    for (const point of points) {
      const last = compact[compact.length - 1];
      if (last && last[0] === point[0] && last[1] === point[1]) continue;
      const before = compact[compact.length - 2];
      if (before && ((before[0] === last[0] && last[0] === point[0])
        || (before[1] === last[1] && last[1] === point[1]))) compact.pop();
      compact.push(point);
    }
    compact.rightSide=rightSide;
    routes.set(key(edge), compact);
    for (let i = 1; i < compact.length; i++) {
      segments.push({a: compact[i - 1], b: compact[i], edge});
    }
  }
  for (const edge of edges) {
    const from = boxes.get(edge.from), to = boxes.get(edge.to);
    if (sameRow(edge)) {
      const y = (Math.max(from.top, to.top) + Math.min(from.bottom, to.bottom)) / 2;
      const rightward = from.left < to.left;
      retain(edge, [[rightward ? from.right : from.left, y],
        [rightward ? to.left - 3 : to.right + 3, y]]);
      continue;
    }
    // Give each source its own input port at the consumer. Equal-column
    // neighbours keep aligned ports and can use a straight vertical arrow.
    const offset = (order.get(edge.from) - 3) * 5;
    const x1 = round(from.left + from.width / 2 + offset);
    const x2 = round(to.left + to.width / 2 + offset);
    const start = [x1, round(from.bottom + 12)];
    const end = [x2, round(to.top - 12)];
    if (longEdge(edge)) {
      const lane = rightLanes.get(edge.from);
      retain(edge, [[x1, from.bottom], start, [lane, start[1]],
        [lane, end[1]], end, [x2, to.top - 3]], true);
      continue;
    }
    endpoints.set(key(edge), {start, end, tail: [x1, from.bottom], tip: [x2, to.top - 3]});
    xs.add(x1); xs.add(x2); ys.add(start[1]); ys.add(end[1]);
  }
  const xValues = [...new Set([...xs].map(round))].filter(x => x >= minX && x <= Math.min(width, right + 12)).sort((a, b) => a - b);
  const yValues = [...new Set([...ys].map(round))].filter(y => y >= 0 && y <= height).sort((a, b) => a - b);
  const nx = xValues.length;
  const xIndex = new Map(xValues.map((x, i) => [x, i]));
  const yIndex = new Map(yValues.map((y, i) => [y, i]));
  const point = id => [xValues[id % nx], yValues[Math.floor(id / nx)]];
  function blocked(a, b) {
    return obstacles.some(box => a[0] === b[0]
      ? a[0] > box.left && a[0] < box.right && Math.max(a[1], b[1]) > box.top && Math.min(a[1], b[1]) < box.bottom
      : a[1] > box.top && a[1] < box.bottom && Math.max(a[0], b[0]) > box.left && Math.min(a[0], b[0]) < box.right);
  }
  const adjacency = Array.from({length: nx * yValues.length}, (_, id) => {
    const ix = id % nx, iy = Math.floor(id / nx), a = point(id);
    return [ix > 0 ? id - 1 : -1, ix < nx - 1 ? id + 1 : -1,
      iy > 0 ? id - nx : -1, iy < yValues.length - 1 ? id + nx : -1]
      .filter(next => next >= 0 && !blocked(a, point(next)));
  });
  function penalty(a, b, edge) {
    let cost = 0;
    const horizontal = a[1] === b[1];
    for (const existing of segments) {
      // A shared source can branch, and a shared target can collect inputs.
      if (existing.edge.from === edge.from || existing.edge.to === edge.to) continue;
      const {a: c, b: d} = existing;
      if (horizontal === (c[1] === d[1])) {
        if ((horizontal && a[1] === c[1]) || (!horizontal && a[0] === c[0])) {
          const axis = horizontal ? 0 : 1;
          const overlap = Math.min(Math.max(a[axis], b[axis]), Math.max(c[axis], d[axis]))
            - Math.max(Math.min(a[axis], b[axis]), Math.min(c[axis], d[axis]));
          if (overlap > 0) cost += overlap * 2;
        }
      } else {
        const h1 = horizontal ? a : c, h2 = horizontal ? b : d;
        const v1 = horizontal ? c : a, v2 = horizontal ? d : b;
        if (v1[0] >= Math.min(h1[0], h2[0]) && v1[0] <= Math.max(h1[0], h2[0])
          && h1[1] >= Math.min(v1[1], v2[1]) && h1[1] <= Math.max(v1[1], v2[1])) cost += 100;
      }
    }
    return cost;
  }
  function search(edge, start, end) {
    const startId = yIndex.get(start[1]) * nx + xIndex.get(start[0]);
    const endId = yIndex.get(end[1]) * nx + xIndex.get(end[0]);
    const distance = new Map(), previous = new Map(), heap = [];
    const heuristic = id => {
      const p = point(id);
      return Math.abs(p[0] - end[0]) + Math.abs(p[1] - end[1]);
    };
    function push(item) {
      let index = heap.length;
      heap.push(item);
      while (index > 0) {
        const parent = (index - 1) >> 1;
        if (heap[parent].score <= item.score) break;
        heap[index] = heap[parent]; index = parent;
      }
      heap[index] = item;
    }
    function pop() {
      const first = heap[0], last = heap.pop();
      if (heap.length) {
        let index = 0;
        while (index * 2 + 1 < heap.length) {
          let child = index * 2 + 1;
          if (child + 1 < heap.length && heap[child + 1].score < heap[child].score) child++;
          if (last.score <= heap[child].score) break;
          heap[index] = heap[child]; index = child;
        }
        heap[index] = last;
      }
      return first;
    }
    const initial = startId * 3;
    distance.set(initial, 0);
    push({state: initial, cost: 0, score: heuristic(startId)});
    while (heap.length) {
      const item = pop(), id = Math.floor(item.state / 3), direction = item.state % 3;
      if (item.cost !== distance.get(item.state)) continue;
      if (id === endId) {
        const result = [];
        for (let state = item.state; state !== undefined; state = previous.get(state)) result.push(point(Math.floor(state / 3)));
        return result.reverse();
      }
      const a = point(id);
      for (const next of adjacency[id]) {
        const b = point(next), nextDirection = a[1] === b[1] ? 1 : 2;
        const cost = item.cost + Math.abs(b[0] - a[0]) + Math.abs(b[1] - a[1])
          + (direction && direction !== nextDirection ? 28 : 0) + penalty(a, b, edge);
        const state = next * 3 + nextDirection;
        if (cost >= (distance.get(state) ?? Infinity)) continue;
        distance.set(state, cost); previous.set(state, item.state);
        push({state, cost, score: cost + heuristic(next)});
      }
    }
    throw new Error('No clear display route for ' + key(edge));
  }
  // Keep geometry stable when selecting cards. Reserve the clearest routes for
  // computation outputs first, then fit the remaining native dependencies.
  const pending = edges.filter(edge => !sameRow(edge) && !longEdge(edge)).sort((a, b) => {
    const rank = edge => computation(edge) ? 0 : edge.from === 'ProofTools' ? 1 : 2;
    return rank(a) - rank(b)
      || (boxes.get(a.to).top - boxes.get(a.from).bottom) - (boxes.get(b.to).top - boxes.get(b.from).bottom);
  });
  for (const edge of pending) {
    const {start, end, tail, tip} = endpoints.get(key(edge));
    retain(edge, [tail, ...search(edge, start, end), tip]);
  }
  return routes;
}

// Small mathematical schematics of the displayed constructions.
function moduleSchematic(id) {
  const grid='<path d="M10 17H54 M10 28H54 M10 39H54 M10 50H54 M10 17V50 M21 17V50 M32 17V50 M43 17V50 M54 17V50" opacity=".35"/>';
  const drawings={
    SpectralSequence: '<path d="M8 20 30 10 54 20 32 30Z M8 30 32 40 54 30 M8 40 32 50 54 40"/><path d="M20 15 44 25 M20 25 44 15 M20 35 44 25 M20 45 44 35" opacity=".45"/>',
    AdamsSynthetic: grid+'<circle cx="32" cy="28" r="4" fill="currentColor" stroke="none"/><path d="M37 24 50 11 M44 11H50V17"/>',
    Literature: '<path d="M8 12H27L32 17 37 12H56V49H37L32 54 27 49H8Z M32 17V54"/><path d="M14 23H25 M14 30H25 M14 37H25 M39 23H50 M39 30H50 M39 37H50" opacity=".45"/>',
    AdamsComputation: grid+'<path d="M16 44H38 M38 44V22"/><circle cx="16" cy="44" r="2.5" fill="currentColor"/><circle cx="38" cy="22" r="2.5" fill="currentColor"/>',
    ProofTools: '<circle cx="12" cy="32" r="5"/><circle cx="50" cy="13" r="5"/><circle cx="50" cy="32" r="5"/><circle cx="50" cy="51" r="5"/><path d="M17 32H45 M17 32 45 13 M17 32 45 51"/>',
    SSComputation: grid+'<path d="M16 44 43 17 M35 17H43V25"/><circle cx="16" cy="44" r="3" fill="currentColor" stroke="none"/>',
    Main: '<path d="M10 21H38 M32 15 38 21 32 27 M10 43H38 M32 37 38 43 32 49" opacity=".5"/><circle cx="47" cy="32" r="13"/><text x="47" y="37" text-anchor="middle" fill="currentColor" stroke="none" font-size="18">∞</text>',
    Geometry: '<ellipse cx="32" cy="32" rx="25" ry="21"/><ellipse cx="32" cy="32" rx="13" ry="21"/><ellipse cx="32" cy="32" rx="25" ry="8"/><path d="M7 32H57 M32 11V53" opacity=".5"/>',
  };
  return '<svg viewBox="0 0 64 64" fill="none" stroke="currentColor" stroke-width="1.1" stroke-linecap="round" stroke-linejoin="round">'+drawings[id]+'</svg>';
}

async function initializeProofMap() {
  const root = document.getElementById('proof-map');
  const presentation = {
  "stages": [
    "Foundations",
    "Literature and initial algebra",
    "Propagation and spectral-sequence results",
    "Permanence and geometry"
  ],
  "nodes": [
    {
      "id": "SpectralSequence",
      "module": "Chapter 01",
      "stage": 0,
      "title": "Define survival precisely",
      "sourceTitle": "Spectral sequences and extensions",
      "summary": "Before using computations, specify how a class passes between pages and what nonzero survival to infinity means. Computation outputs and final theorems use these same notions.",
      "boundary": "Spectral sequences have specified pages, differentials, filtrations and convergence data.",
      "entries": [
        {
          "label": "sem:SpectralSequence:sequence",
          "title": ""
        },
        {
          "label": "sem:SpectralSequence:permanent",
          "title": ""
        },
        {
          "label": "sem:SpectralSequence:convergence",
          "title": ""
        }
      ],
      "inputLabel": "Define",
      "inputs": "Pages, differentials, cycles and boundaries",
      "outputLabel": "Provide",
      "outputs": "Representatives, detection and nonzero permanent survival"
    },
    {
      "id": "AdamsSynthetic",
      "module": "Chapter 02",
      "stage": 0,
      "title": "Specify the systems and classes",
      "sourceTitle": "Adams and synthetic foundations",
      "summary": "The argument uses the same specified classical and synthetic sphere systems throughout. The class h₆² has Adams bidegree (2, 128), hence stem 126. Synthetic objects and λ quotients support the extension and obstruction arguments.",
      "boundary": "The classical and synthetic families use the same specified sphere objects, shifts and comparison maps.",
      "entries": [
        {
          "label": "sem:AdamsSynthetic:categories",
          "title": ""
        },
        {
          "label": "sem:AdamsSynthetic:families",
          "title": ""
        },
        {
          "label": "sem:AdamsSynthetic:standard-classes",
          "title": ""
        }
      ],
      "inputLabel": "Specify",
      "inputs": "Sphere spectra, Adams towers and synthetic objects",
      "outputLabel": "Provide",
      "outputs": "Standard classes hᵢ, products and λ-quotient comparisons"
    },
    {
      "id": "Literature",
      "module": "Chapter 03",
      "stage": 1,
      "title": "Bring in comparison and geometry theorems",
      "sourceTitle": "Literature and comparison inputs",
      "summary": "Literature supplies classical–synthetic comparisons, known differentials and detection results. Main uses vanishing in stem 62 of tmf, low-filtration vanishing, and the specified stem-125 image not annihilated by odd integers in its high-filtration detection argument. Browder’s criterion connects nonzero permanent survival to geometric existence.",
      "boundary": "Literature results are applied with their stated hypotheses and comparisons to the specified model.",
      "entries": [
        {
          "label": "paper:3.6",
          "title": ""
        },
        {
          "label": "sem:Literature:finite-browder",
          "title": ""
        },
        {
          "label": "sem:Literature:tmf-hurewicz",
          "title": ""
        }
      ],
      "inputLabel": "Use",
      "inputs": "Literature results with their full hypotheses",
      "outputLabel": "Provide",
      "outputs": "Comparison and detection inputs, tmf vanishing and image results, and Browder’s criterion"
    },
    {
      "id": "AdamsComputation",
      "module": "Chapter 04",
      "stage": 1,
      "title": "Interpret initial Adams data",
      "sourceTitle": "The E₂ page and direct d₂ computations",
      "summary": "Interpret Lin’s Adams output on the actual sphere and ν-cofiber E₂ pages: bases, coordinates, products and selected classes. Four direct sphere d₂ equations are specified separately from the E₂ algebra.",
      "boundary": "The E₂ comparisons apply through t ≤ 261 on the sphere and t ≤ 200 on the ν-cofiber. ProofTools uses the E₂ algebra; the four direct sphere d₂ equations are computational inputs.",
      "entries": [
        {
          "label": "sem:Computation:table-bases",
          "title": ""
        },
        {
          "label": "sem:AdamsComputation:direct-d2-records",
          "title": ""
        }
      ],
      "program": "Adams",
      "inputLabel": "Use",
      "inputs": "Sphere and ν-cofiber E₂ generators, relations and ordered bases, with their specified comparisons; four direct sphere d₂ equations",
      "outputLabel": "Provide",
      "outputs": "Actual-page coordinates, bases, product statements and direct d₂ inputs",
      "workflow": [
        "Encoded Steenrod-algebra data and specified maps",
        "Resolutions and Ext computation; some d₂ computations also use secondary operations",
        "Sphere E₂ coordinates through t ≤ 261 and ν-cofiber E₂ coordinates through t ≤ 200, with the specified bottom-cell inclusion"
      ]
    },
    {
      "id": "ProofTools",
      "module": "Chapter 05",
      "stage": 2,
      "title": "Prove rules that propagate information",
      "sourceTitle": "Representatives, extensions and comparison laws",
      "summary": "Generalized Leibniz and Mahowald rules derive further differentials and extensions under their full hypotheses. Main also uses extension and representative comparisons. These rules underlie the external program’s propagation strategy.",
      "boundary": "The rules use the E₂ sublayer of AdamsComputation and their specified extension and comparison hypotheses.",
      "entries": [
        {
          "label": "paper:4.6",
          "title": ""
        },
        {
          "label": "sem:ProofTools:finite-strip",
          "title": ""
        }
      ],
      "inputLabel": "Use",
      "inputs": "The specified systems, E₂ algebra and literature comparisons",
      "outputLabel": "Provide",
      "outputs": "Finite-page stretching, extension calculus and generalized propagation rules"
    },
    {
      "id": "SSComputation",
      "module": "Chapter 06",
      "stage": 2,
      "title": "Interpret propagated differential data",
      "sourceTitle": "Eᵣ and dᵣ computations",
      "summary": "Interpret selected ss outputs as differentials, boundaries, finite-page survival or exclusions of differential equations on the sphere and ν-cofiber sequences, for use by Main. The program applies propagation rules to E₂ data and initial differentials.",
      "boundary": "Finite-page representatives feed into the permanence argument, which excludes subsequent outgoing differentials and controls incoming boundaries.",
      "entries": [
        {
          "label": "sem:Computation:table-certification",
          "title": ""
        },
        {
          "label": "paper:7.6",
          "title": ""
        },
        {
          "label": "paper:7.21",
          "title": ""
        }
      ],
      "program": "ss",
      "inputLabel": "Use",
      "inputs": "Specified sphere and ν-cofiber differentials, boundaries, finite-page survival and exclusions of differential equations",
      "outputLabel": "Provide",
      "outputs": "Actual-page differential, boundary and survival inputs for Main",
      "workflow": [
        "Adams output, supplied initial differentials and applicable propagation rules",
        "Leibniz, naturality, cofiber and generalized propagation steps",
        "Differentials, boundaries, finite-page survival and exclusions interpreted on the specified sphere and ν-cofiber sequences"
      ]
    },
    {
      "id": "Main",
      "module": "Chapter 07",
      "stage": 3,
      "title": "Exclude the last possible differential on h₆²",
      "sourceTitle": "The permanence argument",
      "summary": "Page calculations and comparison theorems reduce the last possible outgoing differential to a specified nonzero d₁₂. Literature’s tmf vanishing and image results enter the stem-125 high-filtration detection argument. The local obstruction argument shows that sixth-differential vanishing and the specified η-extension detection cannot both hold, excluding the remaining nonzero d₁₂.",
      "boundary": "The argument uses actual-page computation inputs, detection conditions and specified-model comparisons.",
      "entries": [
        {
          "label": "paper:7.8",
          "title": ""
        },
        {
          "label": "paper:7.9",
          "title": ""
        },
        {
          "label": "paper:1.4",
          "title": ""
        }
      ],
      "inputLabel": "Use",
      "inputs": "Actual-page calculations, extension and detection comparisons, and Literature’s tmf inputs",
      "outputLabel": "Prove",
      "outputs": "The remaining nonzero d₁₂ case is impossible; h₆² survives permanently and nontrivially"
    },
    {
      "id": "Geometry",
      "module": "Chapter 08",
      "stage": 3,
      "title": "Pass from permanence to geometry",
      "sourceTitle": "Framed manifolds of Kervaire invariant one",
      "summary": "Apply Browder’s criterion at j = 6, giving dimension 2⁷ − 2 = 126. The permanence result yields a closed smooth stably framed manifold of Kervaire invariant one. Known low-dimensional cases and HHR nonexistence give the full dimension classification.",
      "boundary": "The deductions use the permanence theorem, the geometric invariant and Browder’s criterion.",
      "entries": [
        {
          "label": "paper:1.1",
          "title": ""
        },
        {
          "label": "paper:1.2",
          "title": ""
        }
      ],
      "inputLabel": "Use",
      "inputs": "Nonzero permanence and Browder; known low-dimensional cases and HHR",
      "outputLabel": "Deduce",
      "outputs": "Existence in dimension 126; the dimensions 2, 6, 14, 30, 62 and 126"
    }
  ]
};
  const response = await fetch(new URL('../Kervaire126/project.json', location.href));
  if (!response.ok) throw new Error('Blueprint data request failed: ' + response.status);
  const project = await response.json();
  const data = {...presentation, edges: moduleDependencies(project, presentation.nodes)};
  const statements = statementAliases(project);
  for (const node of data.nodes) {
    const seen = new Set();
    node.entries = node.entries.flatMap(entry => {
      const statement = statements.get(entry.label);
      if (!statement || seen.has(statement.id)) return [];
      seen.add(statement.id);
      return [{...entry, label: statement.label,
        title: entry.title || statement.title.replace(/\$/g, '').replace(/h_6\^2/g, 'h₆²')}];
    });
  }
  root.querySelector('#proof-map-loading').hidden = true;
  root.querySelector('.kp-count').textContent='Four stages · Eight modules · Inputs, operations and outputs';
  const byId = new Map(data.nodes.map(n => [n.id,n]));
  const flow = root.querySelector('.kp-flow');
  const map = root.querySelector('.kp-map');
  const external = root.querySelector('.kp-external');
  const programPaths = root.querySelector('.kp-program-paths');
  const exchanges = root.querySelector('.kp-exchanges');
  const stagesRoot = root.querySelector('.kp-stages');
  const paths = root.querySelector('.kp-paths');
  const svg = root.querySelector('.kp-edges');
  const buttons = new Map();
  const start = 'AdamsComputation';
  let selected = start;
  let scheduled = 0;
  function element(tag,cls,text) {
    const el = document.createElement(tag);
    if (cls) el.className=cls;
    if (text !== undefined) el.textContent=text;
    return el;
  }
  data.stages.forEach((stage,index) => {
    const section=element('section','kp-stage');
    section.setAttribute('aria-label',stage);section.dataset.stage=String(index);
    const label=element('div','kp-stage-label');
    label.append(element('div','kp-stage-number',String(index+1)),element('div','kp-stage-title',stage));
    const nodes=data.nodes.filter(n=>n.stage===index);
    const row=element('div','kp-row');row.dataset.count=nodes.length;
    nodes.forEach(node=>{
      const button=element('button','kp-node');button.type='button';button.dataset.node=node.id;
      button.setAttribute('aria-pressed','false');button.setAttribute('aria-controls','kp-detail');
      button.setAttribute('aria-label',node.title+'; '+node.module+'; expand chapter details');
      const module=element('span','kp-module');
      module.append(element('span','',node.id));
      const compact = {
        SpectralSequence: 'Pages, differentials, representatives and permanence',
        AdamsSynthetic: 'Specified spheres, standard classes and synthetic comparisons',
        Literature: 'Known results, tmf detection and geometry',
        AdamsComputation: 'E₂ bases, products and selected direct d₂',
        ProofTools: 'Extension and representative comparisons; propagation rules',
        SSComputation: 'Differentials, boundaries, survival and exclusions',
        Main: 'Exclude the last nonzero d₁₂ and obtain permanence',
        Geometry: 'Dimension-126 existence and dimension classification',
      };
      const formulas = {
        SpectralSequence: 'Representatives · Boundaries · E<sub>∞</sub>',
        AdamsSynthetic: 'h<sub>6</sub><sup>2</sup> ∈ E<sub>2</sub><sup>2,128</sup>',
        Literature: 'Browder · tmf · HHR',
        AdamsComputation: 'E<sub>2</sub> · × · d<sub>2</sub>',
        ProofTools: 'Stretching · Leibniz · Mahowald',
        SSComputation: 'E<sub>r</sub> · d<sub>r</sub> · Boundaries · Finite-page survival',
        Main: 'h<sub>6</sub><sup>2</sup> survives nontrivially to E<sub>∞</sub>',
        Geometry: '126 = 2<sup>7</sup> − 2',
      };
      const visual=element('span','kp-node-visual');visual.setAttribute('aria-hidden','true');
      visual.innerHTML=moduleSchematic(node.id);
      const copy=element('span','kp-node-copy');
      const formula=element('span','kp-node-formula');formula.innerHTML=formulas[node.id];
      copy.append(element('span','kp-node-title',node.sourceTitle),element('span','kp-node-subtitle',compact[node.id]),formula);
      const body=element('span','kp-node-body');body.append(visual,copy);button.append(body);
      if (node.program) {
        const handoffs=element('span','kp-node-handoffs');
        data.edges.filter(edge=>edge.from===node.id).forEach(edge=>{
          const target=byId.get(edge.to);
          const short = {
            'AdamsComputation:ProofTools': 'E₂ data',
            'AdamsComputation:SSComputation': 'E₂ and initial calculations',
            'AdamsComputation:Main': 'Product and vanishing constraints',
            'ProofTools:Main': 'Extension and comparison laws',
            'SSComputation:Main': 'Differentials and survival bounds',
            'Main:Geometry': 'Nonzero permanence',
          }[edge.from+':'+edge.to] || 'Specified input';
          const transfer=element('span','kp-output-handoff');
          transfer.dataset.from=node.id;transfer.dataset.to=target.id;
          transfer.append(element('strong','','→ '+target.id),element('span','',short));
          handoffs.append(transfer);
        });
        button.append(handoffs);
      }
      if (node.id === 'Main') {
        const checkpoints=element('span','kp-main-checkpoints');
        for (const [from, label] of [
          ['AdamsComputation','7.8 Detection comparison'],
          ['SSComputation','7.9 Local contradiction'],
        ]) {
          if (!data.edges.some(edge=>edge.from===from&&edge.to==='Main')) continue;
          const checkpoint=element('span','kp-main-checkpoint');
          checkpoint.dataset.input=from;
          checkpoint.append(element('strong','','← '+from),element('span','kp-checkpoint-title',label));
          checkpoints.append(checkpoint);
        }
        button.append(checkpoints);
      }
      if (node.id==='ProofTools') button.append(element('span','kp-method-handoff','→ ss · Propagation rules from the paper'));
      button.append(module,element('span','kp-node-plus','+'));
      button.addEventListener('click',()=>select(node.id,true,selected!==node.id||detail.hidden));
      buttons.set(node.id,button);row.append(button);
    });
    section.append(label,row);stagesRoot.append(section);
  });
  const detail=element('article','kp-detail');detail.id='kp-detail';
  detail.setAttribute('aria-live','polite');
  function select(id,persist=false,expanded=true) {
    if(!byId.has(id)) return;
    selected=id;
    const n=byId.get(id);
    const adjacent=new Set(data.edges.filter(e=>e.from===id||e.to===id).flatMap(e=>[e.from,e.to]));
    buttons.forEach((button,key)=>{
      button.setAttribute('aria-pressed',String(key===id));
      button.setAttribute('aria-expanded',String(key===id&&expanded));
      button.classList.toggle('kp-related',key!==id&&adjacent.has(key));
      button.querySelector('.kp-node-plus').textContent=key===id&&expanded?'−':'+';
    });
    detail.replaceChildren();
    const lead=element('div','kp-detail-lead');
    const close=element('button','kp-detail-close','×');close.type='button';
    close.setAttribute('aria-label','Close chapter details');
    close.addEventListener('click',()=>{select(id,true,false);buttons.get(id).focus();});
    const title=element('h2','',n.sourceTitle.replace(/\$/g,'').replace(/h_6\^2/g,'h₆²'));
    title.id='kp-detail-title';detail.setAttribute('aria-labelledby',title.id);
    detail.append(close);
    lead.append(element('div','kp-detail-label',n.module+' · '+n.id),title,element('p','',n.summary));
    const io=element('dl','kp-detail-io');
    for(const [label,content] of [[n.inputLabel,n.inputs],[n.outputLabel,n.outputs]]) {
      io.append(element('dt','',label),element('dd','',content));
    }
    lead.append(io);
    if(n.id==='Literature'&&data.edges.some(edge=>edge.from==='Literature'&&edge.to==='Main')) {
      const handoff=element('section','kp-math-handoff');
      handoff.append(element('strong','','tmf literature → Main'));
      for(const text of ['π₆₂(tmf) = 0','E₂ˢ,ˢ⁺⁶³(tmf) = 0 (s ≤ 0)','The specified stem-125 image is not annihilated by odd integers']) handoff.append(element('span','',text));
      lead.append(handoff);
    }
    if(n.id==='Main') {
      const checkpoints=element('section','kp-detail-checkpoints');
      checkpoints.append(element('h3','','Computation inputs in the main proof'));
      for(const [from,text] of [
        ['AdamsComputation','Proposition 7.8: products, vanishing and degree constraints enter the detection comparison for the last differential.'],
        ['SSComputation','Candidate exclusions and Proposition 7.9: differentials and survival narrow the possibilities; incoming-differential control on the ν-cofiber contradicts the case forced by the local argument.'],
        ['Literature','tmf vanishing and image results enter high-filtration detection in stem 125.'],
      ]) {
        if(data.edges.some(edge=>edge.from===from&&edge.to==='Main')) checkpoints.append(element('p','','← '+from+' · '+text));
      }
      lead.append(checkpoints);
    }
    if (n.workflow) {
      lead.append(element('h3','','Steps in the external program'));
      const workflow=element('ol','kp-workflow');
      n.workflow.forEach(step=>workflow.append(element('li','',step)));
      lead.append(workflow);
      const source=element('a','','Lin’s program · Source repository ↗');
      source.href='https://github.com/WayneLin92/SSeqCpp';source.target='_blank';source.rel='noopener noreferrer';
      lead.append(source);
    }
    const links=element('div','kp-entry-links');
    n.entries.forEach(entry=>{
      const link=element('a','',entry.title+' ↗');
      link.href='../#/Kervaire126#'+encodeURIComponent(entry.label);
      link.dataset.blueprint=entry.label;
      link.target='_top';link.rel='noopener';links.append(link);
    });
    lead.append(links);
    const scope=element('div','kp-scope');scope.append(element('h3','','How the inputs are used'));
    const transfers=element('ul','kp-transfers');
    data.edges.filter(edge=>edge.from===id||edge.to===id).forEach(edge=>{
      const source=byId.get(edge.from),target=byId.get(edge.to);
      const transfer=element('li','');
      transfer.append(element('strong','',source.id+' → '+target.id),element('span','',handoffDescription(edge)));
      transfers.append(transfer);
    });
    scope.append(transfers,element('h3','','Input chapters'));
    const inputs=element('div','kp-inputs');
    const incoming=data.edges.filter(e=>e.to===id);
    incoming.forEach(edge=>{
      const source=byId.get(edge.from);
      const button=element('button','kp-input',source.title);button.type='button';
      button.addEventListener('click',()=>{select(source.id,true);buttons.get(source.id).scrollIntoView({block:'nearest'});});
      inputs.append(button);
    });
    if(!incoming.length)inputs.append(element('span','kp-caption','Foundational chapter'));
    scope.append(inputs);
    scope.append(element('h3','','Hypotheses and scope'),element('p','kp-open-boundary',n.boundary));
    detail.append(lead,scope);detail.hidden=!expanded;buttons.get(id).closest('.kp-stage').append(detail);
    draw();
    if (persist) {
      const url = new URL(location.href);
      url.hash = expanded ? id : '';
      history.replaceState(null, '', url);
    }
  }
  root.querySelectorAll('[data-select-module]').forEach(button => {
    button.addEventListener('click', () => {
      select(button.dataset.selectModule, true);
      buttons.get(button.dataset.selectModule).scrollIntoView({block:'nearest'});
    });
  });
  function draw() {
    cancelAnimationFrame(scheduled);
    scheduled=requestAnimationFrame(()=>{
      drawProgramTransfers();
      const rect=map.getBoundingClientRect();
      if (!rect.width || !rect.height) return;
      svg.setAttribute('viewBox',`0 0 ${rect.width} ${rect.height}`);
      paths.replaceChildren();
      const localBox = node => {
        const box = node.getBoundingClientRect();
        return {left: box.left - rect.left, right: box.right - rect.left,
          top: box.top - rect.top, bottom: box.bottom - rect.top, width: box.width, height: box.height};
      };
      const boxes = new Map([...buttons].map(([id, button]) => [id, {...localBox(button), stage:byId.get(id).stage}]));
      const labels = [...root.querySelectorAll('.kp-stage-label')].map(localBox);
      if (!detail.hidden) labels.push(localBox(detail));
      const minX = Math.max(0, Math.min(...[...boxes.values()].map(box=>box.left)) - 16);
      const routes = routeModuleEdges(data.edges, boxes, rect.width, rect.height, labels, minX);
      data.edges.forEach(edge=>{
        const points = routes.get(edge.from + ':' + edge.to);
        const d = points.map(([x,y], index) => (index ? 'L ' : 'M ') + x + ' ' + y).join(' ');
        const active=edge.from===selected||edge.to===selected;
        const computation=['AdamsComputation','SSComputation'].includes(edge.from);
        const path=document.createElementNS('http://www.w3.org/2000/svg','path');
        path.setAttribute('d',d);path.setAttribute('fill','none');
        path.setAttribute('stroke',active||computation?'var(--kp-accent)':'var(--kp-edge)');
        path.setAttribute('stroke-width',active?'1.8':computation?'1.4':'1');
        path.setAttribute('opacity',active?'1':computation?'.85':'.35');
        path.setAttribute('marker-end',active||computation?'url(#kp-arrow-active)':'url(#kp-arrow-neutral)');
        path.dataset.from=edge.from;path.dataset.to=edge.to;
        path.classList.toggle('kp-edge-selected',active);
        path.classList.toggle('kp-edge-computation',computation);
        path.classList.toggle('kp-edge-long',Boolean(points.rightSide));
        if (byId.get(edge.to).stage-byId.get(edge.from).stage>1&&!active&&!computation) path.setAttribute('stroke-dasharray','4 5');
        paths.append(path);
      });
    });
  }
  // External record transfers are presentation links, separate from native uses edges.
  function drawProgramTransfers() {
    const rect = flow.getBoundingClientRect();
    exchanges.setAttribute('viewBox', `0 0 ${rect.width} ${rect.height}`);
    programPaths.replaceChildren();
    const workflowPaths = root.querySelector('.kp-program-flow-paths');
    const methodPaths = root.querySelector('.kp-method-paths');
    workflowPaths.replaceChildren();methodPaths.replaceChildren();
    const adams = root.querySelector('[data-program="Adams"]').getBoundingClientRect();
    const ss = root.querySelector('[data-program="ss"]').getBoundingClientRect();
    const flowX = (Math.max(adams.left,ss.left)+Math.min(adams.right,ss.right))/2-rect.left;
    const flowTop = adams.bottom-rect.top+2, flowBottom=ss.top-rect.top-4;
    const workflow = document.createElementNS('http://www.w3.org/2000/svg','path');
    workflow.setAttribute('d',`M ${flowX} ${flowTop} L ${flowX} ${flowBottom}`);
    workflow.setAttribute('marker-end','url(#kp-arrow-program)');
    workflow.dataset.programFrom='Adams';workflow.dataset.programTo='ss';
    const workflowLabel=document.createElementNS('http://www.w3.org/2000/svg','text');
    workflowLabel.setAttribute('x',flowX+9);
    workflowLabel.setAttribute('y',(flowTop+flowBottom)/2+3);
    workflowLabel.textContent='E₂ and initial differentials';
    workflowPaths.append(workflow,workflowLabel);
    const compact = external.getBoundingClientRect().left < map.getBoundingClientRect().right;
    if (compact) return; // Compact views retain explicit handoffs on their cards.
    // This path shows the paper-method correspondence between ProofTools
    // and the external computation, separately from native dependency edges.
    const tools=buttons.get('ProofTools').getBoundingClientRect();
    const methodX=tools.left+tools.width*.7-rect.left;
    const methodEndX=ss.left+ss.width*.24-rect.left;
    const methodY=Math.min(tools.top,ss.top)-rect.top-18;
    const method=document.createElementNS('http://www.w3.org/2000/svg','path');
    method.setAttribute('d',`M ${methodX} ${tools.top-rect.top} L ${methodX} ${methodY} L ${methodEndX} ${methodY} L ${methodEndX} ${ss.top-rect.top-3}`);
    method.setAttribute('marker-end','url(#kp-arrow-method)');
    method.dataset.source='ProofTools';method.dataset.program='ss';
    const methodLabel=document.createElementNS('http://www.w3.org/2000/svg','text');
    methodLabel.setAttribute('x',(methodX+methodEndX)/2);
    methodLabel.setAttribute('y',methodY-7);
    methodLabel.setAttribute('text-anchor','middle');
    methodLabel.textContent='Propagation rules from the paper';
    methodPaths.append(method,methodLabel);
    for (const [program, module, outputs] of [
      ['Adams','AdamsComputation',['E₂ bases and products','Maps and direct d₂']],
      ['ss','SSComputation',['Differentials, boundaries and survival','Specified exclusion records']],
    ]) {
      const source = root.querySelector(`.kp-program-section[data-program="${program}"]`).getBoundingClientRect();
      const target = buttons.get(module).getBoundingClientRect();
      const x1 = source.left - rect.left;
      const x2 = target.right - rect.left + 2;
      // Both cards occupy the same stage. Use their shared vertical span so the
      // two edge ports align even when either card's details change its height.
      const top = Math.max(source.top, target.top);
      const bottom = Math.min(source.bottom, target.bottom);
      const y = (top + bottom) / 2 - rect.top;
      const middle = (x1 + x2) / 2;
      const path = document.createElementNS('http://www.w3.org/2000/svg','path');
      path.setAttribute('d', `M ${x1} ${y} L ${x2} ${y}`);
      path.setAttribute('marker-end','url(#kp-arrow-program)');
      path.dataset.program = program;
      path.dataset.consumer = module;
      const label = document.createElementNS('http://www.w3.org/2000/svg','text');
      label.setAttribute('x', middle);
      label.setAttribute('y', y - 14 * outputs.length);
      label.setAttribute('text-anchor','middle');
      for (const [index, output] of outputs.entries()) {
        const line = document.createElementNS('http://www.w3.org/2000/svg','tspan');
        line.setAttribute('x', middle);
        line.setAttribute('dy', index ? '14' : '0');
        line.textContent = output;
        label.append(line);
      }
      programPaths.append(path,label);
    }
  }
  function restore() {
    let id;
    try { id = decodeURIComponent(location.hash.slice(1)); }
    catch { id = ''; }
    select(byId.has(id) ? id : start, false, byId.has(id));
  }
  restore();
  window.addEventListener('hashchange', restore);
  function resizeHostFrame() {
    if (!window.frameElement) return;
    const height = Math.ceil(root.getBoundingClientRect().height);
    if (window.frameElement.style.height !== height + 'px') {
      window.frameElement.style.height = height + 'px';
    }
  }
  function resize() {
    draw();
    resizeHostFrame();
  }
  root.querySelectorAll('.kp-external details').forEach(panel => {
    panel.addEventListener('toggle', resize);
  });
  new ResizeObserver(resize).observe(root);
  document.fonts?.ready.then(resize);
  resize();
}
initializeProofMap().catch(error => {
  console.error(error);
  const message = document.getElementById('proof-map-loading');
  message.textContent = 'Could not load Blueprint dependencies. Please refresh and try again.';
  message.setAttribute('role', 'alert');
  message.hidden = false;
});
