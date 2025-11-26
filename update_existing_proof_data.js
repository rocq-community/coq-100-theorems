#!/usr/bin/env node

const https = require('https');
const fs = require('fs');

const download = url => new Promise((resolve, reject) => {
  https.get(url, resp => {
    let data = '';
    resp.on('data', (chunk) => { data += chunk; });
    resp.on('end', () => { resolve(data); });
  }).on("error", err => reject(err.message));
});

main = async() => {
  let html = await download("https://www.cs.ru.nl/~freek/100/");
  let current_id = null;
  let current_provers = null;
  let yaml = "";
  for(let line of html.split("\n")) {
    let m;
    // start of theorem
    if(m = line.match(/^<li id="([0-9]*)"/)) {
      console.assert(current_id == null, line);
      current_id = Number(m[1]);
      current_provers = [];
    }
    // end of theorem (can be the same line)
    if(line.match(/^<\/li>$/) || line.match(/^<li id=.*<\/li>$/)) {
      current_provers.sort();
      yaml += current_id + ": [" + current_provers.join(", ") + "]\n";
      current_id = null;
      current_provers = null;
    }
    // inside theorem, seeing <li> and maybe a constructiveness indicator <em>
    if(current_id != null && (m = line.match(/<li>(<em>)?([^,]*),/))) {
      let prover = m[2];
      current_provers.push(prover + (m[1] ? " (constructive)" : ""));
    }
  }
  // data sanity check before overwriting yaml file
  if(yaml.match(/Rocq/g).length >= 50) {
    fs.writeFileSync("existing_proofs.yml", yaml);
  } else {
    console.error("HTML dump:");
    console.error(html);
    console.error("YAML dump:");
    console.error(yaml);
    console.error("Error likely when 'parsing' html (dumps above)");
    process.exit(1);
  }
}

main();
